import Langlands.AlgebraicGeometry.FiniteEtale.PointwiseClosedImmersion
import Langlands.GroupScheme.Cartier.SepClosedCharacterLifting
import Langlands.GroupScheme.Torus.PrimeToCharacteristicCharacters
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Diagonalizing an étale group using its characters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.EtaleMultiplicativeTypeOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (K : Type u) [Field K] [IsSepClosed K]

/-- Liftable characters diagonalize a finite étale commutative group of
prime-to-characteristic order over a separably closed field. -/
theorem exists_diagonalizableIso_of_liftable_characters
    (p : ℕ) [ExpChar K p]
    (G : CommGroupScheme (Spec (CommRingCat.of K)))
    [IsFinite G.X.hom] [Etale G.X.hom]
    (hcard : Nat.Coprime
      (Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)) p)
    (hlift : ∀ φ : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) →* Kˣ,
      ∃ f : G.X ⟶ (Gm _).X,
        (∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          (Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (a ≫ f)).val =
            φ a) ∧
        μ[G.X] ≫ f = (fst G.X G.X ≫ f) * (snd G.X G.X ≫ f)) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (G.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) := by
  classical
  let M := Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X
  have : Finite M := Cartier.finite_points G.X
  obtain ⟨χ, hχ⟩ := PrimeToCharacteristicCharacters.exists_separating_family K p M hcard
  choose f hf hmul using fun i : M => hlift (χ i)
  let ψ : M → (G.toGrp ⟶ (Gm (Spec (CommRingCat.of K))).toGrp) :=
    fun i => homOfPoints
      (fun T => MonoidHom.mk' (fun y => y ≫ f i) fun y z => by
        change lift y z ≫ μ[G.X] ≫ f i = _
        rw [hmul i, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc])
      (fun a y => Category.assoc a y (f i))
  let F : G.toGrp ⟶ splitTorus (Spec (CommRingCat.of K)) M := Pi.lift ψ
  have hcoord (i : M) :
      F.hom.hom ≫ (Pi.π (fun _ : M => (Gm (Spec (CommRingCat.of K))).toGrp) i).hom.hom =
        (ψ i).hom.hom := by
    change (F ≫ Pi.π (fun _ : M => (Gm (Spec (CommRingCat.of K))).toGrp) i).hom.hom = _
    dsimp only [F]
    rw [Pi.lift_comp_π]
  have hinj : Function.Injective
      (fun a : M => a ≫ F.hom.hom) := by
    intro a b hab
    apply hχ
    funext i
    apply Units.ext
    rw [← hf i a, ← hf i b]
    congr 2
    have hi := congrArg
      (fun z => z ≫
        (Pi.π (fun _ : M => (Gm (Spec (CommRingCat.of K))).toGrp) i).hom.hom) hab
    rw [Category.assoc, Category.assoc, hcoord i, comp_homOfPoints,
      comp_homOfPoints] at hi
    exact congrArg (Gm.pointsEquiv _ _) hi
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom (splitTorus (Spec (CommRingCat.of K)) M).X.hom :=
    isAffineHom_splitTorus _ M
  have : IsAffine (splitTorus (Spec (CommRingCat.of K)) M).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of K)) M).X.hom
  have hF : IsClosedSubgroup F :=
    Langlands.AlgebraicGeometry.FiniteEtale.isClosedImmersion_of_injective_points
      F.hom.hom hinj
  exact exists_diagonalizableIso_of_isClosedSubgroup_splitTorus
    (isSplitTorus_splitTorus M) F hF

/-- Finite étale commutative groups of prime-to-characteristic order are
diagonalizable over a separably closed field. -/
theorem exists_diagonalizableIso_of_coprime_order
    (p : ℕ) [ExpChar K p]
    (G : CommGroupScheme (Spec (CommRingCat.of K)))
    [IsFinite G.X.hom] [Etale G.X.hom]
    (hcard : Nat.Coprime
      (Nat.card (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)) p) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (G.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp) :=
  exists_diagonalizableIso_of_liftable_characters K p G hcard
    (Cartier.exists_gm_hom_of_points_of_isSepClosed G)

end Langlands.GroupScheme.EtaleMultiplicativeTypeOrder
