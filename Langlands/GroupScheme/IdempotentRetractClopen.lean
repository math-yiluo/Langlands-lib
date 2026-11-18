import Langlands.GroupScheme.IdempotentRetractLoci

/-! # The clopen identity locus of a fibrewise nontrivial idempotent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} {G : GroupScheme S} (ψ : G ⟶ G)

/-- An identity restriction remains the identity after a specified factorization
through that restriction. -/
theorem baseChange_eq_id_of_factor {U : S.Opens} (b : T ⟶ S) (q : T ⟶ U)
    (hq : q ≫ U.ι = b)
    (h : (baseChange U.ι).map ψ = 𝟙 ((baseChange U.ι).obj G)) :
    (baseChange b).map ψ = 𝟙 ((baseChange b).obj G) := by
  let e := Descent.pullbackComparison U.ι q b hq G
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (baseChange b).map ψ =
        (baseChange q).map ((baseChange U.ι).map ψ) ≫ e.hom :=
      (Descent.pullbackComparison_naturality U.ι q b hq ψ).symm
    _ = e.hom ≫ 𝟙 _ := by rw [h, (baseChange q).map_id, Category.id_comp, Category.comp_id]

/-- A trivial restriction remains trivial after a specified factorization
through that restriction. -/
theorem baseChange_eq_zero_of_factor {U : S.Opens} (b : T ⟶ S) (q : T ⟶ U)
    (hq : q ≫ U.ι = b) (h : (baseChange U.ι).map ψ = 0) :
    (baseChange b).map ψ = 0 := by
  let e := Descent.pullbackComparison U.ι q b hq G
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (baseChange b).map ψ =
        (baseChange q).map ((baseChange U.ι).map ψ) ≫ e.hom :=
      (Descent.pullbackComparison_naturality U.ι q b hq ψ).symm
    _ = e.hom ≫ 0 := by rw [h, Functor.map_zero, zero_comp, comp_zero]

/-- The residue point over a member of an open factors through that open. -/
def residueOpenLift (U : S.Opens) (s : S) (hs : s ∈ U) :
    Spec (CommRingCat.of (S.residueField s)) ⟶ U :=
  IsOpenImmersion.lift U.ι (S.fromSpecResidueField s) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨s, hs⟩, (Scheme.fromSpecResidueField_apply s x).symm⟩)

@[reassoc (attr := simp)]
theorem residueOpenLift_fac (U : S.Opens) (s : S) (hs : s ∈ U) :
    residueOpenLift U s hs ≫ U.ι = S.fromSpecResidueField s :=
  IsOpenImmersion.lift_fac _ _ _

namespace IdempotentRetract

variable {ψ} (P : IdempotentRetract ψ)
  [Smooth G.X.hom] [Smooth P.group.X.hom]
  [GeometricallyConnected G.X.hom] [GeometricallyConnected P.group.X.hom]

/-- The identity and zero opens are disjoint if no residue fibre is trivial. -/
theorem disjoint_identityOpen_zeroOpen
    (hnt : ∀ s : S, (0 : (baseChange (S.fromSpecResidueField s)).obj G ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) ≠ 𝟙 _) :
    Disjoint P.identityOpen P.zeroOpen := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro s hs
  have hi := baseChange_eq_id_of_factor ψ (S.fromSpecResidueField s)
    (residueOpenLift P.identityOpen s hs.1) (residueOpenLift_fac _ _ _)
    P.map_eq_id_on_identityOpen
  have hz := baseChange_eq_zero_of_factor ψ (S.fromSpecResidueField s)
    (residueOpenLift P.zeroOpen s hs.2) (residueOpenLift_fac _ _ _)
    P.map_eq_zero_on_zeroOpen
  exact (hnt s (hz.symm.trans hi)).elim

/-- The identity open is closed once the two residue alternatives cover
the base and are distinct in every residue fibre. -/
theorem isClopen_identityOpen
    (hψ : ∀ s : S, (baseChange (S.fromSpecResidueField s)).map ψ = 0 ∨
      (baseChange (S.fromSpecResidueField s)).map ψ =
        𝟙 ((baseChange (S.fromSpecResidueField s)).obj G))
    (hnt : ∀ s : S, (0 : (baseChange (S.fromSpecResidueField s)).obj G ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) ≠ 𝟙 _) :
    IsClopen (P.identityOpen : Set S) := by
  have hc := P.identityOpen_sup_zeroOpen hψ
  have hd := P.disjoint_identityOpen_zeroOpen hnt
  have hcompl : (P.identityOpen : Set S)ᶜ = P.zeroOpen := by
    ext s
    constructor
    · intro hs
      have hs' : s ∈ P.identityOpen ⊔ P.zeroOpen := by rw [hc]; trivial
      exact hs'.resolve_left hs
    · intro hs hi
      exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) hi hs
  exact ⟨isOpen_compl_iff.mp (hcompl ▸ P.zeroOpen.isOpen), P.identityOpen.isOpen⟩

/-- The actual clopen part of the base on which the idempotent is the identity. -/
def identityClopen
    (hψ : ∀ s : S, (baseChange (S.fromSpecResidueField s)).map ψ = 0 ∨
      (baseChange (S.fromSpecResidueField s)).map ψ =
        𝟙 ((baseChange (S.fromSpecResidueField s)).obj G))
    (hnt : ∀ s : S, (0 : (baseChange (S.fromSpecResidueField s)).obj G ⟶
      (baseChange (S.fromSpecResidueField s)).obj G) ≠ 𝟙 _) :
    TopologicalSpace.Clopens S :=
  ⟨P.identityOpen, P.isClopen_identityOpen hψ hnt⟩

end IdempotentRetract
end Langlands.GroupScheme
