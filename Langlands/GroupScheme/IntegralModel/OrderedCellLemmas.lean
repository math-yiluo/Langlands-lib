import Langlands.GroupScheme.Rational.RootProductTransport
import Langlands.GroupScheme.Rational.OrderedProductBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.IntegralModel

/-! # Ordered products through represented subgroups and integral comparison lemmas -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {B : Scheme.{u}} {G U : GroupScheme B} {n : ℕ} {H : Fin n → GroupScheme B}

/-- The internal ordered multiplication through a represented subgroup `V` is an
isomorphism exactly when every point of `V` is uniquely an ordered product of points of
the represented factor functors, on every test scheme. -/
theorem isIso_orderedMultiplication_factorHom_iff
    {V : SubgroupFunctor G} {jU : U ⟶ G} (hjU : V.IsRepresentedBy jU)
    {F : Fin n → SubgroupFunctor G} (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (F r).IsRepresentedBy (j r))
    (hjV : ∀ r, SubgroupFunctor.range (j r) ≤ V) :
    IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hjV r))) ↔
      ∀ (T : Over B) (g : T ⟶ G.X), g ∈ V.carrier T →
        ∃! x : ∀ r, (F r).carrier T, (List.ofFn fun r => (x r : T ⟶ G.X)).prod = g := by
  have hm : Mono jU.hom.hom := hjU.1
  have hcomp (T : Over B) (y : ∀ r, T ⟶ (H r).X) :
      orderedPoints (fun r => hjU.factorHom (j r) (hjV r)) y ≫ jU.hom.hom =
        (List.ofFn fun r => y r ≫ (j r).hom.hom).prod := by
    rw [orderedPoints_map (fun r => hjU.factorHom (j r) (hjV r)) j jU (fun r => 𝟙 (H r))
      (fun r => by rw [Category.id_comp, SubgroupFunctor.IsRepresentedBy.factorHom_comp])]
    simp only [orderedPoints, Grp.id_hom_hom, Category.comp_id]
  rw [isIso_orderedMultiplication_iff_existsUnique]
  constructor
  · intro h T g hg
    obtain ⟨y, hy, hyu⟩ := h T ((hjU.pointsEquiv T).symm ⟨g, hg⟩)
    have hyg : (List.ofFn fun r => y r ≫ (j r).hom.hom).prod = g := by
      rw [← hcomp, hy, SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
    refine ⟨fun r => (hj r).pointsEquiv T (y r), ?_, ?_⟩
    · simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe] using hyg
    · intro x hx
      have hy' := hyu (fun r => ((hj r).pointsEquiv T).symm (x r)) (by
        apply hm.right_cancellation
        rw [hcomp, SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
        simp only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
        exact hx)
      funext r
      have := congrArg (fun z => (hj r).pointsEquiv T (z r)) hy'
      simpa only [MulEquiv.apply_symm_apply] using this
  · intro h T g'
    have hg : g' ≫ jU.hom.hom ∈ V.carrier T := by
      rw [← hjU.2]
      exact ⟨g', rfl⟩
    obtain ⟨x, hx, hxu⟩ := h T _ hg
    refine ⟨fun r => ((hj r).pointsEquiv T).symm (x r), ?_, ?_⟩
    · apply hm.right_cancellation
      rw [hcomp]
      simp only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp]
      exact hx
    · intro y hy
      have hx' := hxu (fun r => (hj r).pointsEquiv T (y r)) (by
        simp only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe]
        rw [← hcomp, hy])
      funext r
      rw [← hx']
      simp only [MulEquiv.symm_apply_apply]

/-- Isomorphy of internal ordered multiplication is independent of the chosen
representatives of the factor functors and of the ambient subgroup functor. -/
theorem isIso_orderedMultiplication_factorHom_of_isIso
    {V : SubgroupFunctor G} {jU : U ⟶ G} (hjU : V.IsRepresentedBy jU)
    {F : Fin n → SubgroupFunctor G} (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, (F r).IsRepresentedBy (j r))
    (hjV : ∀ r, SubgroupFunctor.range (j r) ≤ V)
    {U' : GroupScheme B} {jU' : U' ⟶ G} (hjU' : V.IsRepresentedBy jU')
    {H' : Fin n → GroupScheme B} (j' : ∀ r, H' r ⟶ G)
    (hj' : ∀ r, (F r).IsRepresentedBy (j' r))
    (hjV' : ∀ r, SubgroupFunctor.range (j' r) ≤ V)
    (h : IsIso (orderedMultiplication (fun r => hjU'.factorHom (j' r) (hjV' r)))) :
    IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hjV r))) :=
  (isIso_orderedMultiplication_factorHom_iff hjU j hj hjV).mpr
    ((isIso_orderedMultiplication_factorHom_iff hjU' j' hj' hjV').mp h)

/-- An actual ordered multiplication isomorphism onto a representative gives the
internal factorization isomorphism. -/
theorem isIso_orderedMultiplication_factorHom_of_iso
    {V : SubgroupFunctor G} {jU : U ⟶ G} (hjU : V.IsRepresentedBy jU)
    (j : ∀ r, H r ⟶ G) (hjV : ∀ r, SubgroupFunctor.range (j r) ≤ V)
    (e : (∏ᶜ H).X ≅ U.X) (he : e.hom ≫ jU.hom.hom = orderedMultiplication j) :
    IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hjV r))) := by
  have hm : Mono jU.hom.hom := hjU.1
  have heq : orderedMultiplication (fun r => hjU.factorHom (j r) (hjV r)) = e.hom := by
    apply hm.right_cancellation
    rw [orderedMultiplication_factorHom hjU j hjV, he]
  rw [heq]
  infer_instance

end RelativeRoot

/-- Negating a cocharacter of a commutative group is inversion of its `Gm` parameter,
over an arbitrary base. -/
theorem groupHom_neg_comp_eq_oppositeCocharacter_overBase {B : Scheme.{u}}
    {T : CommGroupScheme B} {G : GroupScheme B} (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) :
    CommGroupScheme.groupHom (-ν) ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i) := by
  have hν : Gm.powerHom B (-1) ≫ ν = -ν := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [Dynamic.oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom (-ν) ≫ i =
    CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i
  rw [hν]

/-- A positive lattice pairing makes the actual root subgroup lie in the dynamic
unipotent subgroup, over the spectrum of any domain. -/
theorem RelativeRoot.subgroup_le_dynamicUnipotent_of_isDomain {R : Type u} [CommRing R]
    [IsDomain R] {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ν : cocharacterLattice T)
    (ha : 0 < latticePairing T a ν) :
    RelativeRoot.subgroup i a ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  apply RelativeRoot.subgroup_le_dynamicUnipotent_of_power i a ν
    (show 0 < (latticePairing T a ν).toNat by omega)
  change ν ≫ a = ((latticePairing T a ν).toNat : ℤ) • 𝟙 (Gm _)
  rw [Int.toNat_of_nonneg ha.le]
  exact eq_gmEndEquiv_zsmul R (ν ≫ a)

section ClosedImmersion

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
theorem flat_specAlgebraMap : Flat (Spec.algebraMap R K) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))

omit [IsDomain R] in
theorem isSchemeTheoreticallyDominant_specAlgebraMap :
    IsSchemeTheoreticallyDominant (Spec.algebraMap R K) := by
  have hinj : Function.Injective (Spec.algebraMap R K).appTop := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
      (IsFractionRing.injective R K h)
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot _).mp hinj,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

variable {R K}

omit [IsDomain R] in
/-- A closed immersion over the spectrum of a ring into a flat scheme is an
isomorphism when its generic fibre is. -/
theorem isIso_of_isClosedImmersion_of_isIso_pullback
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsClosedImmersion f.left]
    [Flat Y.hom] (hK : IsIso ((Over.pullback (Spec.algebraMap R K)).map f)) :
    IsIso f := by
  let b := Spec.algebraMap R K
  have : IsSchemeTheoreticallyDominant b := isSchemeTheoreticallyDominant_specAlgebraMap R K
  have hdom : IsSchemeTheoreticallyDominant (pullback.fst Y.hom b) := inferInstance
  let fK := (Over.pullback b).map f
  have : IsIso fK := hK
  have hfac : (inv fK).left ≫ pullback.fst X.hom b ≫ f.left = pullback.fst Y.hom b := by
    have h1 : fK.left ≫ pullback.fst Y.hom b = pullback.fst X.hom b ≫ f.left := by
      simp only [fK, Over.pullback_map_left, pullback.lift_fst]
    rw [← h1, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.id_comp]
  have hker : f.left.ker = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hdom.ker_eq_bot, ← hfac, ← Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  have : IsIso f.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have : IsIso ((Over.forget _).map f) := this
  exact isIso_of_reflects_iso f (Over.forget _)

end ClosedImmersion

end Langlands.GroupScheme
