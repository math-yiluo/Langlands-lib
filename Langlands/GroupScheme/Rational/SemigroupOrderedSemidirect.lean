import Langlands.GroupScheme.Rational.SemigroupSemidirect
import Langlands.GroupScheme.Rational.OrderedProductSemidirectAbsorption
import Langlands.GroupScheme.Rational.SemigroupProductRestriction
import Langlands.GroupScheme.SmoothProducts

/-! # Ordered semigroup products in an actual semidirect product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency.types false

namespace SubgroupFunctor.IsRepresentedBy

variable {B : Scheme.{u}} {G H H' : GroupScheme B}
    {F : SubgroupFunctor G} {j : H ⟶ G}

/-- An isomorphism of representatives preserves the exact represented functor. -/
theorem precomp_iso (hj : F.IsRepresentedBy j) (e : H' ≅ H) :
    F.IsRepresentedBy (e.hom ≫ j) := by
  let : Mono j.hom.hom := hj.1
  let eX : H'.X ≅ H.X := (Grp.forget (Over B)).mapIso e
  refine ⟨?_, ?_⟩
  · change Mono (eX.hom ≫ j.hom.hom)
    infer_instance
  · rw [← hj.2]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro z
    constructor
    · rintro ⟨x, hx⟩
      change x ≫ eX.hom ≫ j.hom.hom = z at hx
      refine ⟨x ≫ eX.hom, ?_⟩
      change (x ≫ eX.hom) ≫ j.hom.hom = z
      exact (Category.assoc _ _ _).trans hx
    · rintro ⟨x, hx⟩
      let y : T ⟶ H.X := x
      refine ⟨y ≫ eX.inv, ?_⟩
      change (y ≫ eX.inv) ≫ eX.hom ≫ j.hom.hom = z
      change y ≫ j.hom.hom = z at hx
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hx

end SubgroupFunctor.IsRepresentedBy

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {K G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] [IsAffineHom G.X.hom]
    [Smooth K.X.hom] [Smooth G.X.hom]
    [ConnectedSpace K.X.left] [ConnectedSpace G.X.left]
    (a : AutomorphicAction K G) (b : AutomorphicAction S.toGrp G)
    (hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (q : T ⟶ K.X) (g : T ⟶ G.X), b.act s (a.act q g) = a.act q (b.act s g))
    (hS : IsSplitTorus S.toGrp)
    (hfun : SemigroupFunctorialityStatement.{u})
    (hcomap : ∀ A : AddSubsemigroup (characterLattice S),
      (semigroupSubgroup (a.semidirectLift b hcomm) A).comap a.semidirectInl =
        semigroupSubgroup b A)

section Factors

variable {n : ℕ} (Ψ : Fin n → Set (characterLattice S))
    (H : Fin n → GroupScheme (Spec (CommRingCat.of k))) (j : ∀ i, H i ⟶ G)
    (hj : ∀ i, (semigroupSubgroup b (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy (j i))
    (hstable : ∀ i, a.IsStable (semigroupSubgroup b (AddSubsemigroup.closure (Ψ i))))

/-- Restrict the actual inner action to each supplied normal-factor
semigroup representative. Stability remains an explicit premise. -/
def semigroupInnerActionFamily (i : Fin n) : AutomorphicAction K (H i) :=
  a.onRepresentedSubgroup (j i) (hj i) (hstable i)

omit [IsAffineHom K.X.hom] [Smooth K.X.hom] [Smooth G.X.hom]
  [ConnectedSpace K.X.left] [ConnectedSpace G.X.left] in
theorem semigroupInnerActionFamily_equivariant (i : Fin n)
    (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ K.X) (x : T ⟶ (H i).X) :
    (semigroupInnerActionFamily a b Ψ H j hj hstable i).act q x ≫ (j i).hom.hom =
      a.act q (x ≫ (j i).hom.hom) :=
  a.onRepresentedSubgroup_act_comp (j i) (hj i) (hstable i) q x

include hcomm hS hcomap in
omit [ConnectedSpace G.X.left] in
/-- At a zero-containing block, the induced semidirect map represents the
exact ambient semigroup functor, using the local inverse-image equality
and the supplied stable representative. -/
theorem isRepresentedBy_semigroupInnerSemidirectMap_of_comap (i : Fin n)
    (hzero : 0 ∈ AddSubsemigroup.closure (Ψ i)) :
    (semigroupSubgroup (a.semidirectLift b hcomm)
      (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy
      (AutomorphicAction.semidirectMap
        (semigroupInnerActionFamily a b Ψ H j hj hstable i) a (j i)
        (semigroupInnerActionFamily_equivariant a b Ψ H j hj hstable i)) := by
  have he :
      semigroupSubgroup (a.semidirectLift b hcomm) (AddSubsemigroup.closure (Ψ i)) =
        a.semidirectSubgroup (semigroupSubgroup b (AddSubsemigroup.closure (Ψ i)))
          (hstable i) := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro z
    have hrec := congrArg (fun F : SubgroupFunctor a.semidirectProduct => F.carrier T)
      (a.eq_semidirectSubgroup_comap_inl
        (semigroupSubgroup (a.semidirectLift b hcomm) (AddSubsemigroup.closure (Ψ i)))
        (range_inr_le_semigroupSubgroup_semidirect a b hcomm hS _ hzero))
    change z ∈
        (semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).carrier T ↔
      (a.semidirectPointsEquiv T z).left ∈
        (semigroupSubgroup b (AddSubsemigroup.closure (Ψ i))).carrier T
    rw [hrec]
    change (a.semidirectPointsEquiv T z).left ∈
        ((semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).comap a.semidirectInl).carrier T ↔ _
    rw [hcomap]
  rw [he]
  exact a.isRepresentedBy_semidirectSubgroupInclusion _ (hstable i) (j i) (hj i)

include hcomm hS hfun hcomap hj hstable in
/-- Absorb the acting group at one original zero-containing block. The exact
cross-exclusion condition removes zero from every other generated block. -/
theorem semigroupOrderedSemidirect_of_factors_of_comap
    (hjc : ∀ i, IsClosedSubgroup (j i))
    (hsm : ∀ i, Smooth (H i).X.hom) (hconn : ∀ i, ConnectedSpace (H i).X.left)
    (hcross : ∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)))
    (p : Fin n) (hp : 0 ∈ Ψ p)
    (hprod : IsIso (orderedMultiplication j)) :
    ∃ (R : Fin n → GroupScheme (Spec (CommRingCat.of k)))
      (l : ∀ i, R i ⟶ a.semidirectProduct),
      (∀ i, (semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy (l i) ∧
        IsClosedSubgroup (l i) ∧ Smooth (R i).X.hom ∧ ConnectedSpace (R i).X.left) ∧
      IsIso (orderedMultiplication l) := by
  let c := semigroupInnerActionFamily a b Ψ H j hj hstable
  have heq := semigroupInnerActionFamily_equivariant a b Ψ H j hj hstable
  let R := absorbedSemidirectFamily c p
  let l := absorbedSemidirectMap a c j heq p
  let : IsIso (orderedMultiplication j) := hprod
  refine ⟨R, l, ?_, isIso_orderedMultiplication_absorbedSemidirect a c j heq p⟩
  intro i
  have haff : IsAffineHom (H i).X.hom := by
    let : IsClosedImmersion (j i).hom.hom.left := hjc i
    rw [← (j i).hom.hom.w]
    infer_instance
  by_cases hi : i = p
  · let e := absorbedSemidirectChosenIso c p i hi
    let eX : (R i).X ≅ (H i).X ⊗ K.X := (Grp.forget _).mapIso e
    have hl : l i = e.hom ≫
        AutomorphicAction.semidirectMap (c i) a (j i) (heq i) := by
      dsimp only [l, absorbedSemidirectMap]
      rw [dite_eq_left hi]
    have hz : 0 ∈ AddSubsemigroup.closure (Ψ i) :=
      AddSubsemigroup.subset_closure (hi.symm ▸ hp)
    have hrep := isRepresentedBy_semigroupInnerSemidirectMap_of_comap
      a b hcomm hS hcomap Ψ H j hj hstable i hz
    have hc := a.isClosedSubgroup_semidirectMap (c i) (j i) (heq i) (hjc i)
    have hgeo := smoothConnectedAffineGeometry.2 k (H i) K
      (hsm i) haff (hconn i) inferInstance inferInstance inferInstance
    let : GeometricallyIntegral ((H i).X ⊗ K.X).hom := hgeo.2.2.2
    have hInt : IsIntegral ((H i).X ⊗ K.X).left :=
      GeometricallyIntegral.isIntegral_of_subsingleton ((H i).X ⊗ K.X).hom
    let : IsIntegral ((H i).X ⊗ K.X).left := hInt
    have hcon : ConnectedSpace ((H i).X ⊗ K.X).left := inferInstance
    rw [hl]
    refine ⟨?_, (IsClosedSubgroup.of_iso e).comp hc,
      smooth_of_over_iso eX (smooth_tensor _ _ (hsm i) inferInstance), ?_⟩
    · exact hrep.precomp_iso e
    · exact (eX.hom.left.homeomorph.connectedSpace_iff).mpr hcon
  · let e := absorbedSemidirectUnchangedIso c p i hi
    let eX : (R i).X ≅ (H i).X := (Grp.forget _).mapIso e
    have hl : l i = e.hom ≫ j i ≫ a.semidirectInl := by
      dsimp only [l, absorbedSemidirectMap]
      rw [dite_eq_right hi]
    have hz : 0 ∉ AddSubsemigroup.closure (Ψ i) := by
      intro hz
      exact Set.disjoint_left.mp (hcross p i (Ne.symm hi)) hp hz
    have hr := (hj i).comp
      (show (SubgroupFunctor.range a.semidirectInl).IsRepresentedBy a.semidirectInl from
        ⟨by
          have := a.isClosedSubgroup_semidirectInl.mono
          exact Over.mono_of_mono_left _, rfl⟩)
    rw [← semigroupSubgroup_semidirect_eq_map_of_zero_notMem a b hcomm hS hfun _ hz] at hr
    have hc := (hjc i).comp a.isClosedSubgroup_semidirectInl
    rw [hl]
    refine ⟨?_, (IsClosedSubgroup.of_iso e).comp hc,
      smooth_of_over_iso eX (hsm i), ?_⟩
    · exact hr.precomp_iso e
    · exact (eX.hom.left.homeomorph.connectedSpace_iff).mpr (hconn i)

variable (hinter : SemigroupIntersectionStatement.{u})

include hcomm hS hinter in
theorem isRepresentedBy_semigroupInnerSemidirectMap (i : Fin n)
    (hzero : 0 ∈ AddSubsemigroup.closure (Ψ i)) :
    (semigroupSubgroup (a.semidirectLift b hcomm)
      (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy
      (AutomorphicAction.semidirectMap
        (semigroupInnerActionFamily a b Ψ H j hj hstable i) a (j i)
        (semigroupInnerActionFamily_equivariant a b Ψ H j hj hstable i)) := by
  exact isRepresentedBy_semigroupInnerSemidirectMap_of_comap
    a b hcomm hS (semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter)
    Ψ H j hj hstable i hzero

include hcomm hS hfun hinter hj hstable in
theorem semigroupOrderedSemidirect_of_factors
    (hjc : ∀ i, IsClosedSubgroup (j i))
    (hsm : ∀ i, Smooth (H i).X.hom) (hconn : ∀ i, ConnectedSpace (H i).X.left)
    (hcross : ∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S)))
    (p : Fin n) (hp : 0 ∈ Ψ p)
    (hprod : IsIso (orderedMultiplication j)) :
    ∃ (R : Fin n → GroupScheme (Spec (CommRingCat.of k)))
      (l : ∀ i, R i ⟶ a.semidirectProduct),
      (∀ i, (semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy (l i) ∧
        IsClosedSubgroup (l i) ∧ Smooth (R i).X.hom ∧ ConnectedSpace (R i).X.left) ∧
      IsIso (orderedMultiplication l) := by
  exact semigroupOrderedSemidirect_of_factors_of_comap
    a b hcomm hS hfun (semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter)
    Ψ H j hj hstable hjc hsm hconn hcross p hp hprod

end Factors

include hcomm hS hfun hcomap in
/-- The exact normal-factor ordered-product property gives products for every
larger partitioned support containing zero, under explicit inner stability. -/
theorem semigroupOrderedSemidirect_of_larger_support_of_comap
    (hb : HasOrderedSemigroupProducts b)
    (hstable : ∀ A : AddSubsemigroup (characterLattice S),
      a.IsStable (semigroupSubgroup b A))
    (Ω : Set (characterLattice S)) (hsub : actionWeightSupport b ⊤ ⊆ Ω)
    (hzero : 0 ∈ Ω) (n : ℕ) (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ i, Ψ i) = Ω)
    (hdis : ∀ r s : Fin n, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∃ (R : Fin n → GroupScheme (Spec (CommRingCat.of k)))
      (l : ∀ i, R i ⟶ a.semidirectProduct),
      (∀ i, (semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy (l i) ∧
        IsClosedSubgroup (l i) ∧ Smooth (R i).X.hom ∧ ConnectedSpace (R i).X.left) ∧
      IsIso (orderedMultiplication l) := by
  obtain ⟨H, j, hj, hprod⟩ :=
    hb.for_larger_support Ω hsub n Ψ hcover hdis hcross
  obtain ⟨p, hp, _, _⟩ :=
    WeightPartition.exists_unique_zero_block hcover hcross hzero
  exact semigroupOrderedSemidirect_of_factors_of_comap a b hcomm hS hfun hcomap Ψ H j
    (fun i => (hj i).1) (fun i => hstable _) (fun i => (hj i).2.1)
    (fun i => (hj i).2.2.1) (fun i => (hj i).2.2.2) hcross p hp hprod

variable (hinter : SemigroupIntersectionStatement.{u})

include hcomm hS hfun hinter in
theorem semigroupOrderedSemidirect_of_larger_support
    (hb : HasOrderedSemigroupProducts b)
    (hstable : ∀ A : AddSubsemigroup (characterLattice S),
      a.IsStable (semigroupSubgroup b A))
    (Ω : Set (characterLattice S)) (hsub : actionWeightSupport b ⊤ ⊆ Ω)
    (hzero : 0 ∈ Ω) (n : ℕ) (Ψ : Fin n → Set (characterLattice S))
    (hcover : (⋃ i, Ψ i) = Ω)
    (hdis : ∀ r s : Fin n, r ≠ s → Disjoint (Ψ r) (Ψ s))
    (hcross : ∀ r s : Fin n, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∃ (R : Fin n → GroupScheme (Spec (CommRingCat.of k)))
      (l : ∀ i, R i ⟶ a.semidirectProduct),
      (∀ i, (semigroupSubgroup (a.semidirectLift b hcomm)
          (AddSubsemigroup.closure (Ψ i))).IsRepresentedBy (l i) ∧
        IsClosedSubgroup (l i) ∧ Smooth (R i).X.hom ∧ ConnectedSpace (R i).X.left) ∧
      IsIso (orderedMultiplication l) := by
  exact semigroupOrderedSemidirect_of_larger_support_of_comap
    a b hcomm hS hfun (semigroupSubgroup_semidirect_comap_inl a b hcomm hS hinter)
    hb hstable Ω hsub hzero n Ψ hcover hdis hcross

end RelativeRoot

end Langlands.GroupScheme
