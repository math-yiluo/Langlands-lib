import Langlands.Representation.Families.RenardFamilyFiniteTypeStatements
import Langlands.Representation.Families.RenardFamilyInductionBaseChangeProof
import Langlands.Representation.Exponents.LeviInductionFiniteTypeStatement
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Compact.CharZeroAverage
import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Renard VI.10.7, Variant, last sentence: reduction to the complex VI.7.5 Theorem

Normalized parabolic induction of a smooth `(M(F), B)`-module that is finitely generated over
`B[M(F)]` is finitely generated over `B[G(F)]`, provided normalized parabolic induction of
smooth complex representations preserves finite generation (the complex VI.7.5 Theorem,
`LeviInductionFiniteTypeStatement`). The implication is
`familyLeviInductionFiniteType_of_leviInductionFiniteType`; it keeps the complex statement as a
premise.

The route: the complex span `W` of the `M(F)`-translates of finitely many `B[M(F)]`-generators of
`E` is a finitely generated smooth complex representation whose carrier spans `E` over `B`;
composition with `W ⊆ E` maps the complex induction of `W` equivariantly into the family
induction of `E`; and, because `P(F)\G(F)` is compact, the image spans the family induction over
`B` (averaging over compact open subgroups of `P(F)` and compact double-coset sections).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

universe u uB uE uG uH uV uW

section Generation

variable {B : Type uB} [CommRing B] [Algebra ℂ B] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module B V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Finite generation passes from a complex representation `π` of `H`, finitely generated over
`ℂ[H]`, to a `B`-linear representation `ρ` of `H`, along an additive map `Φ` that is equivariant,
turns complex scalars into their images in `B`, and has image spanning the carrier of `ρ` over
`B`. -/
theorem finite_asModule_of_complexSpan (ρ : Representation B H V) (π : Representation ℂ H W)
    (Φ : W →+ V) (hΦsmul : ∀ (c : ℂ) (w : W), Φ (c • w) = algebraMap ℂ B c • Φ w)
    (hΦ : ∀ (g : H) (w : W), Φ (π g w) = ρ g (Φ w))
    (hspan : Submodule.span B (Set.range Φ) = ⊤)
    (hfg : Module.Finite (MonoidAlgebra ℂ H) π.asModule) :
    Module.Finite (MonoidAlgebra B H) ρ.asModule := by
  classical
  obtain ⟨s, hs⟩ := hfg.fg_top
  let y : Finset ρ.asModule := s.image fun w => Φ w
  let N := Submodule.span (MonoidAlgebra B H) (y : Set ρ.asModule)
  let S := Subrepresentation.ofSubmodule' N
  let C : Subrepresentation π :=
    { toSubmodule :=
        { carrier := {w | Φ w ∈ S.toSubmodule}
          add_mem' := fun {a b} ha hb => by
            change Φ (a + b) ∈ S.toSubmodule
            rw [map_add]
            exact S.toSubmodule.add_mem ha hb
          zero_mem' := by
            change Φ 0 ∈ S.toSubmodule
            rw [map_zero]
            exact S.toSubmodule.zero_mem
          smul_mem' := fun c w hw => by
            change Φ (c • w) ∈ S.toSubmodule
            rw [hΦsmul]
            exact S.toSubmodule.smul_mem _ hw }
      apply_mem_toSubmodule := fun g w hw => by
        change Φ (π g w) ∈ S.toSubmodule
        rw [hΦ]
        exact S.apply_mem_toSubmodule g hw }
  have hle : Submodule.span (MonoidAlgebra ℂ H) (s : Set π.asModule) ≤ C.asSubmodule := by
    apply Submodule.span_le.mpr
    intro w hw
    change Φ w ∈ N
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  have hrange : Submodule.span B (Set.range Φ) ≤ S.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hw : (show π.asModule from w) ∈ C.asSubmodule := hle (hs.symm ▸ Submodule.mem_top)
    exact hw
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    have hx : (show V from x) ∈ Submodule.span B (Set.range Φ) := by
      rw [hspan]
      exact Submodule.mem_top
    exact hrange hx
  exact ⟨⟨y, hN⟩⟩

variable {k : Type uB} [CommRing k] {X : Type uV} [AddCommGroup X] [Module k X]

/-- The subrepresentation spanned over the coefficients by all translates of a set. -/
def translateSpan (ρ : Representation k H X) (s : Set X) : Subrepresentation ρ where
  toSubmodule := Submodule.span k (Set.range fun x : H × s => ρ x.1 (x.2 : X))
  apply_mem_toSubmodule g v hv := by
    have hle : Submodule.span k (Set.range fun x : H × s => ρ x.1 (x.2 : X)) ≤
        (Submodule.span k (Set.range fun x : H × s => ρ x.1 (x.2 : X))).comap (ρ g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨h, e⟩, rfl⟩
      change ρ g (ρ h (e : X)) ∈ Submodule.span k (Set.range fun x : H × s => ρ x.1 (x.2 : X))
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨(g * h, e), rfl⟩
    exact hle hv

theorem subset_translateSpan (ρ : Representation k H X) (s : Set X) {e : X} (he : e ∈ s) :
    e ∈ (translateSpan ρ s).toSubmodule :=
  Submodule.subset_span ⟨(1, ⟨e, he⟩), by simp⟩

/-- The span of the translates of a finite set is finitely generated over the group algebra. -/
theorem finite_translateSpan (ρ : Representation k H X) (s : Finset X) :
    Module.Finite (MonoidAlgebra k H)
      (translateSpan ρ (s : Set X)).toRepresentation.asModule := by
  classical
  let S := translateSpan ρ (s : Set X)
  let R := S.toRepresentation
  let gen : {x // x ∈ (s : Set X)} → R.asModule := fun e =>
    R.asModuleEquiv.symm ⟨e.1, subset_translateSpan ρ (s : Set X) e.2⟩
  let y : Finset R.asModule := s.attach.image fun e => gen ⟨e.1, Finset.mem_coe.mpr e.2⟩
  let N := Submodule.span (MonoidAlgebra k H) (y : Set R.asModule)
  let T := Subrepresentation.ofSubmodule' N
  have hgen : ∀ (g : H) (e : (s : Set X)),
      (⟨ρ g (e : X), S.apply_mem_toSubmodule g (subset_translateSpan ρ (s : Set X) e.2)⟩ :
        S.toSubmodule) ∈ T.toSubmodule := by
    intro g e
    have h1 : gen e ∈ N :=
      Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨⟨e.1, e.2⟩, Finset.mem_attach _ _, rfl⟩))
    exact T.apply_mem_toSubmodule g h1
  have hall : ∀ (v : X) (hv : v ∈ S.toSubmodule), (⟨v, hv⟩ : S.toSubmodule) ∈ T.toSubmodule := by
    intro v hv
    change v ∈ Submodule.span k (Set.range fun x : H × (s : Set X) => ρ x.1 (x.2 : X)) at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, e⟩, rfl⟩ := hx
      exact hgen g e
    | zero => exact T.toSubmodule.zero_mem
    | add a b _ _ ha hb => exact T.toSubmodule.add_mem ha hb
    | smul c a _ ha => exact T.toSubmodule.smul_mem c ha
  have hN : N = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    exact hall (R.asModuleEquiv x).1 (R.asModuleEquiv x).2
  exact ⟨⟨y, hN⟩⟩

variable [TopologicalSpace H]

/-- A subrepresentation of a smooth representation is smooth. -/
theorem isSmooth_toRepresentation {ρ : Representation k H X} (hρ : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := by
  intro w
  obtain ⟨K, hK⟩ := hρ (w : X)
  exact ⟨K, fun g => Subtype.ext (hK g)⟩

end Generation

section Comparison

open Langlands.Jacquet.CoefficientRestriction

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] (P : Subgroup G)
  {E : Type uE} [AddCommGroup E] [Module B E] [Module ℂ E] [IsScalarTower ℂ B E]
  (τ : Representation B P E) {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (τW : Representation ℂ P W) (incl : W →ₗ[ℂ] E)
  (hincl : ∀ (p : P) (w : W), incl (τW p w) = τ p (incl w))

include hincl in
/-- Composition with the complex-linear map `incl`, from the smooth induction of `τW` to the
smooth induction of the family `τ`. -/
def inducedComparison :
    Induction.SmoothFunctions P τW →+ Induction.SmoothFunctions P τ where
  toFun f := by
    refine ⟨⟨fun x => incl (Induction.eval P τW f x), ?_⟩, ?_⟩
    · intro p x
      change incl (f.1.1 ((p : G) * x)) = τ p (incl (f.1.1 x))
      exact (congrArg incl (f.1.property p x)).trans (hincl p _)
    · obtain ⟨K, hK⟩ := f.property
      refine ⟨K, fun k => ?_⟩
      apply Subtype.ext
      funext x
      exact congrArg incl (congrArg (fun a : Induction.EquivariantFunctions P τW => a.1 x) (hK k))
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_zero incl
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact map_add incl _ _

omit [Algebra ℂ B] [IsScalarTower ℂ B E] in
@[simp] theorem eval_inducedComparison (f : Induction.SmoothFunctions P τW) (x : G) :
    Induction.eval P τ (inducedComparison P τ τW incl hincl f) x = incl (Induction.eval P τW f x) :=
  rfl

/-- The comparison turns complex scalars into their images in `B`. -/
theorem inducedComparison_smul (c : ℂ) (f : Induction.SmoothFunctions P τW) :
    inducedComparison P τ τW incl hincl (c • f) = algebraMap ℂ B c • inducedComparison P τ τW incl hincl f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change incl (c • Induction.eval P τW f x) = algebraMap ℂ B c • incl (Induction.eval P τW f x)
  rw [map_smul, algebraMap_smul]

omit [Algebra ℂ B] [IsScalarTower ℂ B E] in
/-- The comparison intertwines right translation. -/
theorem inducedComparison_equivariant [IsTopologicalGroup G] (g : G)
    (f : Induction.SmoothFunctions P τW) :
    inducedComparison P τ τW incl hincl (Induction.smoothInduced P τW g f) =
      Induction.smoothInduced P τ g (inducedComparison P τ τW incl hincl f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

variable {P τ τW incl}

omit [Algebra ℂ B] [TopologicalSpace G] [IsScalarTower ℂ B E] in
include hincl in
/-- An injective equivariant map from `τW` into a smooth representation makes `τW` smooth. -/
theorem isSmooth_of_injective [TopologicalSpace P] (hinj : Function.Injective incl)
    (hτ : IsSmooth τ) : IsSmooth τW := by
  intro w
  obtain ⟨K, hK⟩ := hτ (incl w)
  refine ⟨K, fun k => hinj ?_⟩
  change incl (τW (k : P) w) = incl w
  rw [hincl]
  exact hK k

variable [IsTopologicalGroup G]

include hincl in
/-- Averaging over a compact open subgroup `H` of `P`: if the carrier of `E` is spanned over
`B` by the image of `incl`, every `H`-fixed vector of `E` lies in the `B`-span of the image of the
`H`-fixed vectors of `W`. -/
theorem mem_span_image_fixedVectors (hτ : IsSmooth τ) (hτW : IsSmooth τW)
    (hspan : Submodule.span B (Set.range incl) = ⊤) (H : OpenSubgroup P)
    (hH : IsCompact (H : Set P)) {v : E} (hv : v ∈ fixedVectors τ H.toSubgroup) :
    v ∈ Submodule.span B (incl '' (fixedVectors τW H.toSubgroup : Set W)) := by
  let τC := complexRepresentation τ
  have hτC : IsSmooth τC := (isSmooth_complexRepresentation τ).2 hτ
  let A := Compact.CharZero.averageMap τC hτC H hH
  let AW := Compact.CharZero.averageMap τW hτW H hH
  let T : τW.IntertwiningMap τC := incl.intertwiningMap_of_isIntertwiningMap τW τC fun p w => hincl p w
  have hT : ∀ w : W, A (incl w) = incl (AW w) := fun w =>
    (LinearMap.congr_fun (Compact.CharZero.averageMap_commute τW τC hτW hτC H hH T) w).symm
  have hB : ∀ (b : B) (x : E), A (b • x) = b • A x := by
    intro b x
    let Lb : E →ₗ[ℂ] E :=
      { toFun := fun y => b • y
        map_add' := smul_add b
        map_smul' := fun c y => smul_comm b c y }
    let Tb : τC.IntertwiningMap τC :=
      Lb.intertwiningMap_of_isIntertwiningMap τC τC fun p y => ((τ p).map_smul b y).symm
    exact (LinearMap.congr_fun (Compact.CharZero.averageMap_commute τC τC hτC hτC H hH Tb) x).symm
  have key : ∀ x : E, A x ∈ Submodule.span B (incl '' (fixedVectors τW H.toSubgroup : Set W)) := by
    intro x
    have hx : x ∈ Submodule.span B (Set.range incl) := by
      rw [hspan]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [hT]
      exact Submodule.subset_span
        ⟨AW w, Compact.CharZero.averageMap_mem_fixedVectors τW hτW H hH w, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [hB]
      exact Submodule.smul_mem _ c ha
  have hAv : A v = v := Compact.CharZero.averageMap_id τC hτC H hH v (fun h => hv h)
  rw [← hAv]
  exact key v

variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [CompactSpace (Induction.LeftQuotient P)]

omit [IsTopologicalGroup G] in
/-- If `P \ G` is compact and the carrier of `E` is spanned over `B` by the image of `incl`, the
image of the comparison map spans the family induction over `B`. -/
theorem span_range_inducedComparison (hP : IsClosed (P : Set G)) (hτ : IsSmooth τ)
    (hτW : IsSmooth τW) (hspan : Submodule.span B (Set.range incl) = ⊤) :
    Submodule.span B (Set.range (inducedComparison P τ τW incl hincl)) = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro f
  obtain ⟨K, hKc, hfK⟩ := exists_isCompact_fixedVectors (Induction.smoothInduced_smooth P τ f)
  obtain ⟨t, hcover, hdistinct⟩ := Induction.exists_finset_doubleCoset_representatives P K
  let S := Submodule.span B (Set.range (inducedComparison P τ τW incl hincl))
  have hsec : ∀ (i : t) (v : E),
      v ∈ Submodule.span B
        (incl '' (fixedVectors τW (Induction.conjOpenSubgroup P K i).toSubgroup : Set W)) →
      ∃ F ∈ S, F ∈ fixedVectors (Induction.smoothInduced P τ) K.toSubgroup ∧
        ∀ j : t, Induction.eval P τ F j = if j = i then v else 0 := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      let s := Induction.fixedDoubleCosetSection P τW K hKc i ⟨w, hw⟩
      refine ⟨inducedComparison P τ τW incl hincl s.1, Submodule.subset_span ⟨s.1, rfl⟩, ?_, ?_⟩
      · intro k
        change Induction.smoothInduced P τ (k : G) (inducedComparison P τ τW incl hincl s.1) =
          inducedComparison P τ τW incl hincl s.1
        rw [← inducedComparison_equivariant]
        exact congrArg _ (s.2 k)
      · intro j
        rw [eval_inducedComparison]
        split_ifs with hji
        · subst hji
          rw [Induction.fixedDoubleCosetSection_eval_self]
        · rw [Induction.fixedDoubleCosetSection_eval_of_ne, map_zero]
          intro he
          exact hji (hdistinct he)
    | zero =>
      refine ⟨0, S.zero_mem, (fixedVectors _ _).zero_mem, fun j => ?_⟩
      rw [ite_self]
      rfl
    | add a b _ _ ha hb =>
      obtain ⟨Fa, hFaS, hFaK, hFa⟩ := ha
      obtain ⟨Fb, hFbS, hFbK, hFb⟩ := hb
      refine ⟨Fa + Fb, S.add_mem hFaS hFbS, (fixedVectors _ _).add_mem hFaK hFbK, fun j => ?_⟩
      change Induction.eval P τ Fa j + Induction.eval P τ Fb j = _
      rw [hFa, hFb]
      split_ifs
      · rfl
      · exact add_zero 0
    | smul c a _ ha =>
      obtain ⟨Fa, hFaS, hFaK, hFa⟩ := ha
      refine ⟨c • Fa, S.smul_mem c hFaS, (fixedVectors _ _).smul_mem c hFaK, fun j => ?_⟩
      change c • Induction.eval P τ Fa j = _
      rw [hFa]
      split_ifs
      · rfl
      · exact smul_zero c
  have hval : ∀ i : t, Induction.eval P τ f i ∈ Submodule.span B
      (incl '' (fixedVectors τW (Induction.conjOpenSubgroup P K i).toSubgroup : Set W)) :=
    fun i => mem_span_image_fixedVectors hincl hτ hτW hspan _
      (isCompact_conjOpenSubgroup hP K hKc i) (Induction.eval_mem_fixedVectors P τ K i hfK)
  choose F hFS hFK hF using fun i : t => hsec i _ (hval i)
  have hmem : (∑ i : t, F i) ∈ fixedVectors (Induction.smoothInduced P τ) K.toSubgroup :=
    Submodule.sum_mem _ fun i _ => hFK i
  have hsum : (∑ i : t, F i) = f := by
    have heq : Induction.fixedEvaluation P τ K t ⟨_, hmem⟩ =
        Induction.fixedEvaluation P τ K t ⟨f, hfK⟩ := by
      funext j
      apply Subtype.ext
      change inducedEval P τ (j : G) (∑ i : t, F i) = Induction.eval P τ f j
      rw [map_sum]
      change ∑ i : t, Induction.eval P τ (F i) j = Induction.eval P τ f j
      simp_rw [hF]
      exact Fintype.sum_ite_eq j fun i : t => Induction.eval P τ f i
    exact congrArg Subtype.val (Induction.fixedEvaluation_injective P τ K t hcover heq)
  rw [← hsum]
  exact S.sum_mem fun i _ => hFS i

end Comparison

section Levi

open Langlands.Jacquet.CoefficientRestriction
open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance reductionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.10.7, Variant, last sentence, for one represented parabolic `P = MN` with
compact `P(F)\G(F)`, assuming that complex normalized induction `i_P^G` takes finitely
generated smooth representations of `M(F)` on carriers in `Type uE` to finitely generated
ones: the family induction of a smooth `(M(F), B)`-module finitely generated over `B[M(F)]`
is finitely generated over `B[G(F)]`. -/
theorem finite_leviInducedRepresentation_of_complex (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (hcomplex : letI := leviPointTopology l hl
      ∀ ρ : SmoothRep.{0, u, uE} ℂ (rationalPoints M),
        Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) ρ.representation.asModule →
          Module.Finite (MonoidAlgebra ℂ (rationalPoints G))
            ((leviInductionFunctor.{u, uE} p l r hp hr hl hmul).obj ρ).representation.asModule)
    {B : Type uB} [CommRing B] [Algebra ℂ B]
    {E : Type uE} [AddCommGroup E] [Module B E] (σ : Representation B (rationalPoints M) E)
    (hσ : letI := leviPointTopology l hl; IsSmooth σ)
    (hfg : Module.Finite (MonoidAlgebra B (rationalPoints M)) σ.asModule) :
    Module.Finite (MonoidAlgebra B (rationalPoints G))
      (leviInducedRepresentation p l r hp hr hl hmul σ).asModule := by
  classical
  let := leviPointTopology l hl
  let : Module ℂ E := Module.compHom E (algebraMap ℂ B)
  have : IsScalarTower ℂ B E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hP : IsClosed (pointImage p : Set (rationalPoints G)) :=
    isClosed_pointImage p hp.isClosedSubgroup
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hδ : IsUnimodularModulus (pointImage (r ≫ p)) hU :=
    isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  let e := leviPointsEquiv p l hp hl
  let σC := complexRepresentation σ
  obtain ⟨s, hs⟩ := hfg.fg_top
  let s' : Finset E := s.image σ.asModuleEquiv
  let Wsub := translateSpan σC (s' : Set E)
  have hWsm : IsSmooth Wsub.toRepresentation :=
    isSmooth_toRepresentation ((isSmooth_complexRepresentation σ).2 hσ) Wsub
  let Wsm : SmoothRep.{0, u, uE} ℂ (rationalPoints M) := SmoothRep.of Wsub.toRepresentation hWsm
  have hWfin : Module.Finite (MonoidAlgebra ℂ (rationalPoints M)) Wsm.representation.asModule :=
    finite_translateSpan σC s'
  have hfin := hcomplex Wsm hWfin
  let incl : Wsub.toSubmodule →ₗ[ℂ] E := Wsub.toSubmodule.subtype
  have hχ : ∀ q : pointImage p,
      ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage p)
          h.le_normalizer q : ℂˣ) : ℂ) =
        ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage (l ≫ p))
          h.levi_le_normalizer (h.projection q) : ℂˣ) : ℂ) := fun q => by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ]
    rfl
  have hincl : ∀ (q : pointImage p) (w : Wsub.toSubmodule),
      incl (Langlands.Aubert.General.inducingRepresentation h hU
          (SmoothRep.pullback e.symm Wsm) q w) =
        Langlands.Renard.AlgebraicFamily.inducingRepresentation h hU
          (leviImageRepresentation p l hp hl σ) q (incl w) := by
    intro q w
    change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage p)
          h.le_normalizer q : ℂˣ) : ℂ) • σ (e.symm (h.projection q)) (w : E) =
        algebraMap ℂ B ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU
          (pointImage (l ≫ p)) h.levi_le_normalizer (h.projection q) : ℂˣ) : ℂ) •
          σ (e.symm (h.projection q)) (w : E)
    rw [hχ q]
    rfl
  have hspanE : Submodule.span B (Set.range incl) = ⊤ := by
    let N : Submodule B E := Submodule.span B (Set.range incl)
    let Nrep : Subrepresentation σ :=
      { toSubmodule := N
        apply_mem_toSubmodule := fun g v hv => by
          have hle : N ≤ N.comap (σ g) := by
            apply Submodule.span_le.mpr
            rintro _ ⟨w, rfl⟩
            show σ g (incl w) ∈ N
            exact Submodule.subset_span ⟨Wsub.toRepresentation g w, rfl⟩
          exact hle hv }
    have htop : (⊤ : Submodule (MonoidAlgebra B (rationalPoints M)) σ.asModule) ≤
        Nrep.asSubmodule := by
      rw [← hs]
      apply Submodule.span_le.mpr
      intro x hx
      show σ.asModuleEquiv x ∈ N
      exact Submodule.subset_span ⟨⟨σ.asModuleEquiv x, subset_translateSpan σC (s' : Set E)
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))⟩, rfl⟩
    rw [Submodule.eq_top_iff']
    intro x
    exact htop (Submodule.mem_top : σ.asModuleEquiv.symm x ∈ ⊤)
  have hτ := isSmooth_leviInducingRepresentation p l r hp hl hr hmul σ hσ
  have hτW : IsSmooth (Langlands.Aubert.General.inducingRepresentation h hU
      (SmoothRep.pullback e.symm Wsm)) :=
    isSmooth_of_injective hincl Wsub.toSubmodule.injective_subtype hτ
  exact finite_asModule_of_complexSpan (leviInducedRepresentation p l r hp hr hl hmul σ)
    ((leviInductionFunctor p l r hp hr hl hmul).obj Wsm).representation
    (inducedComparison (pointImage p) _ _ incl hincl)
    (inducedComparison_smul (pointImage p) _ _ incl hincl)
    (inducedComparison_equivariant (pointImage p) _ _ incl hincl)
    (span_range_inducedComparison hincl hP hτ hτW hspanE) hfin

end Levi

section Statement

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- Renard VI.10.7, Variant, last sentence, from the complex VI.7.5 Theorem: if normalized
parabolic induction preserves finitely generated smooth complex representations (with Levi
carriers in `Type uE`), it preserves smooth `(M(F), B)`-modules finitely generated over
`B[M(F)]`. -/
theorem familyLeviInductionFiniteType_of_leviInductionFiniteType
    (H : LeviInductionFiniteTypeStatement.{u, uE}) :
    FamilyLeviInductionFiniteTypeStatement.{u, uB, uE} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  intro B _ _ _ _ _ E _ _ σ hσ _ hfg
  let := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  exact finite_leviInducedRepresentation_of_complex p l r hp hl hr hmul
    (H k G hG P M U p l r hp hl hr hmul) σ hσ hfg

end Statement

end Langlands.Renard.AlgebraicFamily
