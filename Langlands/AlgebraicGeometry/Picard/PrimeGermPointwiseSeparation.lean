import Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionStatement
import Langlands.AlgebraicGeometry.Picard.StalkTangent
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.LinearSystem.DualNumberPoints
import Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalksProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AbelianScheme.AlgebraicallyClosedCommonAffineProof
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Pointwise separation conditional on prime-germ divisor sections -/

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.AlgebraicGeometry.LinearSystem

namespace PrimeGermSeparation

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Transport the local map of a local-ring-valued point to a specified image point. -/
def stalkMapAt {R : Type u} [CommRing R] [IsLocalRing R]
    (g : Spec (CommRingCat.of R) ⟶ X) (e : X)
    (he : g (IsLocalRing.closedPoint R) = e) : X.presheaf.stalk e ⟶ CommRingCat.of R :=
  (X.presheaf.stalkCongr (by rw [he]; rfl)).hom ≫ Scheme.stalkClosedPointTo g

lemma spec_stalkMapAt {R : Type u} [CommRing R] [IsLocalRing R]
    (g : Spec (CommRingCat.of R) ⟶ X) (e : X)
    (he : g (IsLocalRing.closedPoint R) = e) :
    Spec.map (stalkMapAt g e he) ≫ X.fromSpecStalk e = g := by
  subst e
  simpa [stalkMapAt] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk g

lemma stalkMapAt_germ {R : Type u} [CommRing R] [IsLocalRing R]
    (g : Spec (CommRingCat.of R) ⟶ X) (e : X)
    (he : g (IsLocalRing.closedPoint R) = e) (U : X.Opens) (heU : e ∈ U)
    (hg : ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) :
    (stalkMapAt g e he) (X.presheaf.germ U e heU f) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (g.appLE U ⊤ hg f) := by
  subst e
  have h := Scheme.germ_stalkClosedPointTo g U heU
  have hm : (((Spec (CommRingCat.of R)).presheaf.mapIso
      (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem g heU).symm).op).hom) =
      (Spec (CommRingCat.of R)).presheaf.map (homOfLE hg).op := by
    rw [Functor.mapIso_hom]
    apply congrArg (fun i => (Spec (CommRingCat.of R)).presheaf.map i)
    exact Subsingleton.elim _ _
  simp only [Iso.trans_hom, hm, ← Category.assoc] at h
  have hh := congrArg (fun k : Γ(X, U) ⟶ CommRingCat.of R => k f) h
  simpa [stalkMapAt, Scheme.Hom.appLE] using hh

/-- A nonconstant augmented dual-number algebra map detects an element of the
augmentation ideal. -/
lemma exists_augmentation_zero_map_ne_zero {A : Type u} [CommRing A] [Algebra K A]
    (r : A →ₐ[K] K) (f : A →ₐ[K] DualNumber K)
    (hne : f ≠ (TrivSqZeroExt.inlAlgHom K K K).comp r) :
    ∃ b : A, r b = 0 ∧ f b ≠ 0 := by
  have hx : ∃ a : A, f a ≠ algebraMap K (DualNumber K) (r a) := by
    by_contra h
    apply hne
    apply AlgHom.ext
    intro a
    exact not_exists_not.mp h a
  obtain ⟨a, ha⟩ := hx
  refine ⟨a - algebraMap K A (r a), ?_, ?_⟩
  · simp
  · simpa only [map_sub, AlgHom.commutes, sub_ne_zero] using ha

lemma tangent_closedPoint_eq
    {p : X ⟶ Spec (CommRingCat.of K)}
    {z : Spec (CommRingCat.of K) ⟶ X}
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X}
    (ht : IsTangentVectorAt p z t) :
    t (IsLocalRing.closedPoint (DualNumber K)) = z (IsLocalRing.closedPoint K) := by
  rw [← ht.2, Scheme.Hom.comp_apply]
  congr 1
  have := subsingleton_spec_dualNumber (K := K)
  exact Subsingleton.elim _ _

/-- The algebra map on the rational stalk induced by an actual tangent vector. -/
def tangentStalkAlgHom (p : X ⟶ Spec (CommRingCat.of K))
    (z : Spec (CommRingCat.of K) ⟶ X)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X)
    (ht : IsTangentVectorAt p z t) :
    letI := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
    X.presheaf.stalk (z (IsLocalRing.closedPoint K)) →ₐ[K] DualNumber K := by
  let := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
  refine Spec.homEquivAlgHom
    ⟨Spec.map (stalkMapAt t _ (tangent_closedPoint_eq ht)), ?_⟩
  rw [spec_algebraMap_stalkAlgebraOver, ← Category.assoc, spec_stalkMapAt]
  exact ht.1

lemma tangentStalkAlgHom_toRingHom (p : X ⟶ Spec (CommRingCat.of K))
    (z : Spec (CommRingCat.of K) ⟶ X)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X)
    (ht : IsTangentVectorAt p z t) :
    letI := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
    (tangentStalkAlgHom p z t ht).toRingHom =
      (stalkMapAt t _ (tangent_closedPoint_eq ht)).hom := by
  let := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
  change (Spec.preimage (Spec.map _)).hom = _
  rw [Spec.preimage_map]

lemma tangentStalkAlgHom_spec_comp (p : X ⟶ Spec (CommRingCat.of K))
    (z : Spec (CommRingCat.of K) ⟶ X)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X)
    (ht : IsTangentVectorAt p z t) :
    letI := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
    Spec.map (CommRingCat.ofHom (tangentStalkAlgHom p z t ht).toRingHom) ≫
      X.fromSpecStalk (z (IsLocalRing.closedPoint K)) = t := by
  let := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
  rw [tangentStalkAlgHom_toRingHom]
  change Spec.map (stalkMapAt t _ (tangent_closedPoint_eq ht)) ≫ _ = t
  exact spec_stalkMapAt t _ (tangent_closedPoint_eq ht)

/-- A nonzero tangent vector detects a nonzero nonunit in the rational stalk. -/
lemma exists_nonunit_stalk_detected
    (p : X ⟶ Spec (CommRingCat.of K))
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : IsRationalPoint p z)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X)
    (ht : IsNonzeroTangentVectorAt p z t) :
    ∃ b : X.presheaf.stalk (z (IsLocalRing.closedPoint K)),
      ¬ IsUnit b ∧
      (stalkMapAt t _ (tangent_closedPoint_eq ht.1)) b ≠ 0 := by
  let := stalkAlgebraOver p (z (IsLocalRing.closedPoint K))
  let r := rationalStalkAugmentation p z hz
  let f := tangentStalkAlgHom p z t ht.1
  have hne : f ≠ (TrivSqZeroExt.inlAlgHom K K K).comp r := by
    intro h
    apply ht.2
    rw [← tangentStalkAlgHom_spec_comp p z t ht.1,
      (spec_map_eq_constant_tangent_iff r f).mpr h, Category.assoc,
      rationalStalkAugmentation_spec_comp p z hz]
  obtain ⟨b, hb, hfb⟩ := exists_augmentation_zero_map_ne_zero r f hne
  refine ⟨b, ?_, ?_⟩
  · intro hu
    have hi := hu.map r.toRingHom
    change IsUnit (r b) at hi
    rw [hb] at hi
    exact not_isUnit_zero hi
  · change f.toRingHom b ≠ 0 at hfb
    rwa [tangentStalkAlgHom_toRingHom] at hfb

/-- At a rational point, a prime-germ section vanishes. -/
lemma vanishes_of_not_mem (L : LineBundle X) (s : GlobalSections L.obj)
    (z : Spec (CommRingCat.of K) ⟶ X)
    (hz : z (IsLocalRing.closedPoint K) ∉ trivializationOpen L.obj s) :
    VanishesAlong L z s :=
  (vanishesAlong_iff_not_mem z s).mpr hz

section points

variable [IsAlgClosed K] [IsIntegral X] [IsLocallyNoetherian X]
    (hS1 : PrimeGermDivisorSectionStatement.{u})
    (hfactorial : ∀ e : X, UniqueFactorizationMonoid (X.presheaf.stalk e))
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]

omit [IsLocallyNoetherian X] in
/-- A nonempty generation open supplies a rational point where the section is nonzero. -/
lemma exists_rational_nonvanishing (L : LineBundle X) (s : GlobalSections L.obj)
    (hne : (trivializationOpen L.obj s : Set X).Nonempty) :
    ∃ y, IsRationalPoint p y ∧ ¬ VanishesAlong L y s := by
  obtain ⟨y, hy, hys⟩ :=
    Langlands.GroupScheme.SeparatingLineBundle.exists_rationalPoint_mem_of_isOpen
      p (fun _ : Unit => (trivializationOpen L.obj s : Set X))
      (fun _ => (trivializationOpen L.obj s).isOpen) (fun _ => hne)
  refine ⟨y, hy, ?_⟩
  rw [vanishesAlong_iff_not_mem]
  exact not_not.mpr (hys ())

include hS1 hfactorial in
/-- A prime factor of a function vanishing at one point and invertible at the other
gives a separating section. -/
lemma separate_point
    (z x : Spec (CommRingCat.of K) ⟶ X) (hz : IsRationalPoint p z)
    (hx : IsRationalPoint p x) (hne : x ≠ z)
    (U : X.Opens) (hU : IsAffineOpen U)
    (hzU : z (IsLocalRing.closedPoint K) ∈ U)
    (hxU : x (IsLocalRing.closedPoint K) ∈ U) :
    ∃ (L : LineBundle X) (s : GlobalSections L.obj),
      VanishesAlong L z s ∧
      (∃ y, IsRationalPoint p y ∧ ¬ VanishesAlong L y s) ∧
      ¬ VanishesAlong L x s := by
  classical
  let e := z (IsLocalRing.closedPoint K)
  let a := x (IsLocalRing.closedPoint K)
  have heClosed : IsClosed ({e} : Set X) := (pointEquivClosedPoint p ⟨z, hz⟩).2
  have hae : a ≠ e := fun h => hne (ext_of_apply_closedPoint_eq p hx hz h)
  let V : X.Opens := ⟨{e}ᶜ, heClosed.isOpen_compl⟩
  have haV : a ∈ V := hae
  obtain ⟨f, hfV, haf⟩ := hU.exists_basicOpen_le (⟨a, haV⟩ : V) hxU
  have hef : e ∉ X.basicOpen f := fun h => (hfV h : e ≠ e) rfl
  have hf : f ≠ 0 := by
    intro h
    have hi := (X.mem_basicOpen f a hxU).mp haf
    rw [h, map_zero] at hi
    exact not_isUnit_zero hi
  have hgerm : X.presheaf.germ U e hzU f ≠ 0 := by
    intro h
    apply hf
    apply germ_injective_of_isIntegral X e hzU
    simpa using h
  have hnonunit : ¬ IsUnit (X.presheaf.germ U e hzU f) :=
    fun h => hef ((X.mem_basicOpen f e hzU).mpr h)
  let := hfactorial e
  obtain ⟨π, hπ, hπf⟩ := WfDvdMonoid.exists_irreducible_factor hnonunit hgerm
  obtain ⟨L, s, hes, _, hbasic, _⟩ := hS1 X hfactorial e π hπ.prime
  have hxs : ¬ VanishesAlong L x s := by
    rw [vanishesAlong_iff_not_mem]
    exact not_not.mpr (hbasic U hzU f hπf haf)
  exact ⟨L, s, vanishes_of_not_mem L s z hes, ⟨x, hx, hxs⟩, hxs⟩

include hS1 hfactorial in
/-- A prime factor detected by a nonzero tangent vector gives a section detecting
that vector. -/
lemma separate_tangent
    (z : Spec (CommRingCat.of K) ⟶ X) (hz : IsRationalPoint p z)
    (t : Spec (CommRingCat.of (DualNumber K)) ⟶ X)
    (ht : IsNonzeroTangentVectorAt p z t) :
    ∃ (L : LineBundle X) (s : GlobalSections L.obj),
      VanishesAlong L z s ∧
      (∃ y, IsRationalPoint p y ∧ ¬ VanishesAlong L y s) ∧
      ¬ VanishesAlong L t s := by
  classical
  let e := z (IsLocalRing.closedPoint K)
  let φ := stalkMapAt t e (tangent_closedPoint_eq ht.1)
  obtain ⟨b, hb, hφb⟩ := exists_nonunit_stalk_detected p z hz t ht
  have hb0 : b ≠ 0 := by
    intro h
    exact hφb (by rw [h, map_zero])
  let := hfactorial e
  obtain ⟨π, hπ, hπb⟩ := WfDvdMonoid.exists_irreducible_factor hb hb0
  have hφπ : φ π ≠ 0 := by
    intro h
    apply hφb
    rcases hπb with ⟨c, rfl⟩
    change φ (π * c) = 0
    rw [map_mul, h, zero_mul]
  obtain ⟨L, s, hes, hnonempty, _, V, heV, a, ha, hvanishes⟩ :=
    hS1 X hfactorial e π hπ.prime
  have htV : ⊤ ≤ t ⁻¹ᵁ V :=
    fun τ _ => forall_mem_of_augmentation_comp ht.1.2 heV τ
  have hφa : φ (X.presheaf.germ V e heV a) ≠ 0 :=
    (ha.map φ.hom).ne_zero_iff.mpr hφπ
  have hta : t.appLE V ⊤ htV a ≠ 0 := by
    intro h
    apply hφa
    change (stalkMapAt t e (tangent_closedPoint_eq ht.1))
      (X.presheaf.germ V e heV a) = 0
    rw [stalkMapAt_germ t e (tangent_closedPoint_eq ht.1) V heV htV, h, map_zero]
  exact ⟨L, s, vanishes_of_not_mem L s z hes,
    exists_rational_nonvanishing p L s hnonempty,
    fun h => hta ((hvanishes _ t htV).mp h)⟩

end points

end PrimeGermSeparation

/-- Prime-germ divisor sections give the two pointwise separation hypotheses for
finite seed extraction on a smooth proper geometrically connected commutative
group scheme. -/
theorem separation_of_primeGermDivisorSection
    (hS1 : PrimeGermDivisorSectionStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K]
    (G : Grp (Over (Spec (CommRingCat.of K)))) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsProper G.X.hom] [GeometricallyConnected G.X.hom]
    (z : Spec (CommRingCat.of K) ⟶ G.X.left) (hz : IsRationalPoint G.X.hom z) :
    (∀ x, IsRationalPoint G.X.hom x → x ≠ z →
      ∃ (L : LineBundle G.X.left) (s : GlobalSections L.obj),
        VanishesAlong L z s ∧
        (∃ y, IsRationalPoint G.X.hom y ∧ ¬ VanishesAlong L y s) ∧
        ¬ VanishesAlong L x s) ∧
    (∀ t, IsNonzeroTangentVectorAt G.X.hom z t →
      ∃ (L : LineBundle G.X.left) (s : GlobalSections L.obj),
        VanishesAlong L z s ∧
        (∃ y, IsRationalPoint G.X.hom y ∧ ¬ VanishesAlong L y s) ∧
        ¬ VanishesAlong L t s) := by
  have : IrreducibleSpace G.X.left :=
    Langlands.GroupScheme.SeparatingLineBundle.irreducibleSpace_of_smooth_of_isProper G
  have : AlgebraicGeometry.IsReduced G.X.left :=
    SmoothReducedProof.isReduced_of_smooth_over_field K G.X.left G.X.hom
  have : IsIntegral G.X.left := isIntegral_of_irreducibleSpace_of_isReduced G.X.left
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have hfactorial : ∀ e : G.X.left, UniqueFactorizationMonoid (G.X.left.presheaf.stalk e) :=
    smoothAlgClosedFactorialStalks K G.X.left G.X.hom inferInstance
  constructor
  · intro x hx hne
    obtain ⟨U, hU, hzU, hxU⟩ :=
      Langlands.GroupScheme.algebraicallyClosedCommonAffine K G
        inferInstance inferInstance inferInstance
        (z (IsLocalRing.closedPoint K)) (x (IsLocalRing.closedPoint K))
        (pointEquivClosedPoint G.X.hom ⟨z, hz⟩).2
        (pointEquivClosedPoint G.X.hom ⟨x, hx⟩).2
    exact PrimeGermSeparation.separate_point hS1 hfactorial G.X.hom z x hz hx hne
      U hU hzU hxU
  · exact fun t ht =>
      PrimeGermSeparation.separate_tangent hS1 hfactorial G.X.hom z hz t ht

end Langlands.AlgebraicGeometry.Picard
