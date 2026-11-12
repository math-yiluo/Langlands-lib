import Langlands.Representation.CuspidalSupport.SplitReflector
import Langlands.Representation.CuspidalSupport.BernsteinCuspAdjunctionStatement
import Langlands.Representation.CuspidalSupport.BernsteinCuspidalSupportExistence
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Aubert.General.CuspidalQuotientEmbedding
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The functor `R` of Renard VI.7.2: exactness, finite type, faithfulness, injective units -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport.BernsteinCuspLeftAdjoint

open SmoothRep Langlands.Aubert.General.ExactnessDetection

section Generic

universe uG uW

variable {H : Type uG} [Group H] [TopologicalSpace H]

/-- The pair `(𝟙 X, 𝟙 X)` is short exact exactly when `X` is zero. -/
theorem isShortExact_id_id_iff (X : SmoothRep.{0, uG, uW} ℂ H) :
    IsShortExact (hom (𝟙 X)) (hom (𝟙 X)) ↔ Subsingleton X := by
  constructor
  · rintro ⟨-, -, hex⟩
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ LinearMap.ker (hom (𝟙 X)).toLinearMap := hex ▸ ⟨a, rfl⟩
    have hb : b ∈ LinearMap.ker (hom (𝟙 X)).toLinearMap := hex ▸ ⟨b, rfl⟩
    rw [LinearMap.mem_ker] at ha hb
    change a = 0 at ha
    change b = 0 at hb
    rw [ha, hb]
  · intro hX
    refine ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨y, Subsingleton.elim _ _⟩, ?_⟩
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => ⟨x, Subsingleton.elim _ _⟩⟩

/-- A functor preserving actual short exact sequences sends zero objects to
zero objects. -/
theorem subsingleton_obj {H' : Type uG} [Group H'] [TopologicalSpace H']
    (Φ : SmoothRep.{0, uG, uW} ℂ H ⥤ SmoothRep.{0, uG, uW} ℂ H')
    (hΦ : ∀ {A B C : SmoothRep.{0, uG, uW} ℂ H} (f : A ⟶ B) (g : B ⟶ C),
      IsShortExact (hom f) (hom g) → IsShortExact (hom (Φ.map f)) (hom (Φ.map g)))
    {X : SmoothRep.{0, uG, uW} ℂ H} (hX : Subsingleton X) : Subsingleton (Φ.obj X) := by
  have h := hΦ (𝟙 X) (𝟙 X) ((isShortExact_id_id_iff X).2 hX)
  rw [CategoryTheory.Functor.map_id] at h
  exact (isShortExact_id_id_iff _).1 h

/-- A right adjoint preserves monomorphisms. -/
theorem mono_map_of_adjunction {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {X Y : D} (m : X ⟶ Y) [Mono m] : Mono (R.map m) :=
  ⟨fun g h H => by
    apply (adj.homEquiv _ _).symm.injective
    rw [← cancel_mono m, ← adj.homEquiv_naturality_right_symm,
      ← adj.homEquiv_naturality_right_symm, H]⟩

end Generic

universe uF uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance bernsteinCuspLeftAdjointTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The cuspidal representations of the standard Levi `M_J`, at carrier universe
`uW`: those whose proper standard normalized Jacquet modules inside `M_J` vanish. -/
abbrev cusp (J : Finset (SimpleRoot i ν)) :
    ObjectProperty (SmoothRep.{0, uF, uW} ℂ (levi i ν J)) := fun W =>
  Langlands.Aubert.General.IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) family.closedUnipotent J
    (family.closedLevi J) (family.leviDecomposition J) W

/-- The normalized Jacquet functor `r_{P_J}^G`, at carrier universe `uW`. -/
abbrev jac (J : Finset (SimpleRoot i ν)) :
    SmoothRep.{0, uF, uW} ℂ (rationalPoints G) ⥤ SmoothRep.{0, uF, uW} ℂ (levi i ν J) :=
  jacquetFunctor (family.decomposition J) (family.closedUnipotent J)

/-- The functor `R : V ↦ (r_{P_J}^G(V)_sc)_J` for a family `sc` of functors to the
cuspidal subcategories. -/
abbrev bernsteinR
    (sc : ∀ J : Finset (SimpleRoot i ν),
      SmoothRep.{0, uF, uW} ℂ (levi i ν J) ⥤ (cusp.{uF, uW} family J).FullSubcategory) :
    SmoothRep.{0, uF, uW} ℂ (rationalPoints G) ⥤
      (∀ J : Finset (SimpleRoot i ν), (cusp.{uF, uW} family J).FullSubcategory) :=
  Functor.pi' fun J => jac family J ⋙ sc J

omit [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)] in
include family in
/-- The standard unipotent radicals are limits of compact subgroups. -/
theorem unipotent_isLimitOfCompactSubgroups (J : Finset (SimpleRoot i ν)) :
    Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν J) :=
  standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement i ν
    standardCocharacter family.connectedReductive family.maximalSplitTorus
    family.genericCocharacter J

/-- Each standard normalized Jacquet functor preserves actual short exact sequences. -/
theorem jac_map_isShortExact (J : Finset (SimpleRoot i ν))
    {A B C : SmoothRep.{0, uF, uW} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsShortExact (hom f) (hom g)) :
    IsShortExact (hom ((jac family J).map f)) (hom ((jac family J).map g)) :=
  jacquetFunctor_map_isShortExact (family.decomposition J) (family.closedUnipotent J)
    (unipotent_isLimitOfCompactSubgroups family J) f g hfg

/-- The cuspidal property of a standard Levi is closed under subrepresentations and
quotients; with splittings it is split Serre. -/
theorem isSplitSerre_cusp (J : Finset (SimpleRoot i ν))
    (hsplit : ∀ A, SplitReflector.HasSplitting (cusp.{uF, uW} family J) A) :
    SplitReflector.IsSplitSerre (cusp.{uF, uW} family J) where
  of_injective f hf hB :=
    Langlands.Aubert.General.IsLeviCuspidal.of_isSubquotient (fun K =>
      isLimitOfCompactSubgroups_subgroupOf _ _ (family.closedLevi J)
        (unipotent_isLimitOfCompactSubgroups family (leviIndex J K)))
      hB (IsSubrepresentation.isSubquotient ⟨f, hf⟩)
  of_surjective f hf hA := Langlands.Aubert.General.IsLeviCuspidal.of_surjective hA f hf
  splitting := hsplit

variable {family}
variable {sc : ∀ J : Finset (SimpleRoot i ν),
      SmoothRep.{0, uF, uW} ℂ (levi i ν J) ⥤ (cusp.{uF, uW} family J).FullSubcategory}

/-- `R` is exact componentwise. -/
theorem bernsteinR_map_isShortExact
    (hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, uW} family J))
    (adj : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    {A B C : SmoothRep.{0, uF, uW} ℂ (rationalPoints G)} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsShortExact (hom f) (hom g)) (J : Finset (SimpleRoot i ν)) :
    IsShortExact (hom (((bernsteinR family sc).map f) J).hom)
      (hom (((bernsteinR family sc).map g) J).hom) :=
  SplitReflector.map_isShortExact (hQ J) (adj J) _ _
    (jac_map_isShortExact family J f g hfg)

/-- Every component of `R` sends zero objects to zero objects. -/
theorem bernsteinR_obj_subsingleton
    (hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, uW} family J))
    (adj : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    {X : SmoothRep.{0, uF, uW} ℂ (rationalPoints G)} (hX : Subsingleton X)
    (J : Finset (SimpleRoot i ν)) : Subsingleton (((bernsteinR family sc).obj X) J).obj :=
  subsingleton_obj (jac family J ⋙ sc J ⋙ (cusp.{uF, uW} family J).ι)
    (fun f g hfg => bernsteinR_map_isShortExact hQ adj f g hfg J) hX

/-- Conservativity of `R` (the argument of Renard's proof of faithfulness): a
nonzero representation has a nonzero component of `R`. A standard index of minimal
cardinality with nonzero Jacquet module gives a cuspidal Jacquet module, on which
the unit of the cuspidal-part adjunction is injective. -/
theorem exists_nontrivial_bernsteinR_obj
    (adj : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    (V : SmoothRep.{0, uF, uW} ℂ (rationalPoints G)) [Nontrivial V] :
    ∃ J, Nontrivial (((bernsteinR family sc).obj V) J).obj := by
  have := family.maximalSplitTorus.isSplitSubtorus.mono
  have hRoots : HasRelativeRootSystem i :=
    relativeRootSystem F G family.connectedReductive T i family.maximalSplitTorus
  obtain ⟨J, hJ, hcusp⟩ :=
    exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier i ν standardCocharacter
      standardLeviIntersection hRoots family.connectedReductive family.maximalSplitTorus
      family.genericCocharacter family.closedUnipotent family.closedLevi V
  refine ⟨J, ?_⟩
  have hinj := SplitReflector.unit_injective_of_mem (adj J)
    (A := (jac family J).obj V) hcusp
  exact @Function.Injective.nontrivial _ _ hJ _ hinj

/-- For every right adjoint `I'` of `R` and every adjunction, every unit morphism
`V → I'(R(V))` is injective (Renard VI.7.2, second Lemma (iii)). -/
theorem bernsteinR_unit_injective
    (hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, uW} family J))
    (adjJ : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    {I' : (∀ J : Finset (SimpleRoot i ν), (cusp.{uF, uW} family J).FullSubcategory) ⥤
      SmoothRep.{0, uF, uW} ℂ (rationalPoints G)}
    (adj : bernsteinR family sc ⊣ I') (V : SmoothRep.{0, uF, uW} ℂ (rationalPoints G)) :
    Function.Injective (hom (adj.unit.app V)) := by
  let R := bernsteinR family sc
  let ηV := adj.unit.app V
  let S := (hom ηV).ker
  let K := subrepresentation V S
  let incl : K ⟶ V := subtype V S
  -- `R` sends the kernel inclusion to a monomorphism.
  have hmono : Mono (R.map incl) := by
    refine ⟨fun g h H => funext fun J => ?_⟩
    have hinj : Function.Injective (hom ((R.map incl) J).hom) :=
      (bernsteinR_map_isShortExact hQ adjJ incl (mkQ V S) (subtype_mkQ_isShortExact V S) J).1
    have : Mono ((cusp.{uF, uW} family J).ι.map ((R.map incl) J)) :=
      (Langlands.SmoothRep.mono_iff_injective _).2 hinj
    have : Mono ((R.map incl) J) := (cusp.{uF, uW} family J).ι.mono_of_mono_map this
    exact (cancel_mono ((R.map incl) J)).1 (congr_fun H J)
  have hIinj : Function.Injective (hom (I'.map (R.map incl))) :=
    (Langlands.SmoothRep.mono_iff_injective _).1 (mono_map_of_adjunction adj (R.map incl))
  -- The unit at the kernel vanishes.
  have hK0 : ∀ k : K, hom (adj.unit.app K) k = 0 := by
    intro k
    apply hIinj
    have hnat := congrArg (fun t => hom t k) (adj.unit.naturality incl)
    change hom ηV (hom incl k) = hom (I'.map (R.map incl)) (hom (adj.unit.app K) k) at hnat
    rw [← hnat, map_zero]
    exact k.2
  -- Hence every component of `R K` vanishes.
  have hRK : ∀ J, Subsingleton ((R.obj K) J).obj := by
    intro J
    let etaK := adj.unit.app K
    have hD : Subsingleton (SmoothRep.image etaK) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      rw [← hx, ← hy]
      exact (hK0 x).trans (hK0 y).symm
    have hDR := bernsteinR_obj_subsingleton hQ adjJ hD J
    have hid : R.map (imageProjection etaK) ≫ (adj.homEquiv (SmoothRep.image etaK) (R.obj K)).symm (imageι etaK) =
        𝟙 (R.obj K) := by
      rw [← adj.homEquiv_naturality_left_symm]
      change (adj.homEquiv K (R.obj K)).symm etaK = 𝟙 (R.obj K)
      rw [Equiv.symm_apply_eq, adj.homEquiv_unit, CategoryTheory.Functor.map_id]
      exact (Category.comp_id _).symm
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun t => hom (t J).hom a) hid
    have hb := congrArg (fun t => hom (t J).hom b) hid
    change hom (((adj.homEquiv (SmoothRep.image etaK) (R.obj K)).symm (imageι etaK)) J).hom
      (hom ((R.map (imageProjection etaK)) J).hom a) = a at ha
    change hom (((adj.homEquiv (SmoothRep.image etaK) (R.obj K)).symm (imageι etaK)) J).hom
      (hom ((R.map (imageProjection etaK)) J).hom b) = b at hb
    rw [← ha, ← hb, Subsingleton.elim (hom ((R.map (imageProjection etaK)) J).hom a)]
  -- By conservativity the kernel vanishes.
  have hKs : Subsingleton K := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    obtain ⟨J, hJ⟩ := exists_nontrivial_bernsteinR_obj adjJ K
    exact (not_nontrivial_iff_subsingleton.2 (hRK J)) hJ
  intro x y hxy
  have hmem : x - y ∈ S := by
    change hom ηV (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have h0 : (⟨x - y, hmem⟩ : K) = 0 := @Subsingleton.elim _ hKs _ _
  exact sub_eq_zero.1 (congrArg Subtype.val h0)

/-- `R` is faithful whenever it has a right adjoint. -/
theorem bernsteinR_faithful
    (hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, uW} family J))
    (adjJ : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    {I' : (∀ J : Finset (SimpleRoot i ν), (cusp.{uF, uW} family J).FullSubcategory) ⥤
      SmoothRep.{0, uF, uW} ℂ (rationalPoints G)}
    (adj : bernsteinR family sc ⊣ I') : (bernsteinR family sc).Faithful := by
  have : ∀ X, Mono (adj.unit.app X) := fun X =>
    (Langlands.SmoothRep.mono_iff_injective _).2 (bernsteinR_unit_injective hQ adjJ adj X)
  exact adj.faithful_L_of_mono_unit_app

/-- `R` sends representations of finite type to families of representations of
finite type. -/
theorem bernsteinR_obj_finite
    (hQ : ∀ J, SplitReflector.IsSplitSerre (cusp.{uF, uW} family J))
    (adjJ : ∀ J, sc J ⊣ (cusp.{uF, uW} family J).ι)
    (V : SmoothRep.{0, uF, uW} ℂ (rationalPoints G))
    (hV : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) V.representation.asModule)
    (J : Finset (SimpleRoot i ν)) :
    Module.Finite (MonoidAlgebra ℂ (levi i ν J))
      (((bernsteinR family sc).obj V) J).obj.representation.asModule := by
  let := (family.closedLevi J).locallyCompactSpace
  let := compactSpace_leftQuotient_parabolic i ν
    BruhatTits.dynamicParabolicQuotientCompact standardCocharacter
    family.connectedReductive family.maximalSplitTorus family.genericCocharacter J
  have hjac : Module.Finite (MonoidAlgebra ℂ (levi i ν J))
      ((jac family J).obj V).representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient
      (family.decomposition J) (family.closedUnipotent J) V hV
  exact Module.Finite.of_surjective (hM := hjac)
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (hom ((adjJ J).unit.app ((jac family J).obj V))))
    (SplitReflector.unit_surjective (hQ J) (adjJ J) _)

end Langlands.CuspidalSupport.BernsteinCuspLeftAdjoint
