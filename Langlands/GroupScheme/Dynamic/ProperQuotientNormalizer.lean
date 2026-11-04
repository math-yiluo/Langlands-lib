import Langlands.GroupScheme.Dynamic.NonfixedFlagQuotientSection
import Langlands.GroupScheme.Dynamic.NonidentityNormalizerFromProperQuotient

/-! # Nonidentity normalizers from proper homogeneous quotient geometry -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- A proper homogeneous quotient of a proper stabilizer, with an exact
coordinate-line stabilizer presentation, yields a nonidentity Weyl
representative without a supplied nonfixed point. -/
def nonidentityNormalizerOfProperFlagQuotient
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    [Finite (relativeWeylGroup i)]
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hconj : MaximalToriAreConjugate P)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (n : ℕ) (ρ : MatrixRepresentation G (Fin (n + 1))) (l : Fin (n + 1))
    (hstab : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (SubgroupFunctor.range j).carrier V ↔
        ∃ c : Γ(V.left, ⊤)ˣ,
          (ρ.pointMatrix V x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(V.left, ⊤)) *ᵥ
              Pi.single l 1 =
            (c : Γ(V.left, ⊤)) • (Pi.single l (1 : Γ(V.left, ⊤)) :
              Fin (n + 1) → Γ(V.left, ⊤))) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  let g := Dynamic.nonfixedFlagQuotientLift i hi j hj f hf hc hconj hproper q hfib
  exact nonidentityNormalizerOfNonfixedProperFlagQuotient i hi j hj f hf hc hconj q
    hfib n ρ l hstab g.val g.property

/-- Pairwise dependence of the actual roots supplies the finite Weyl
quotient needed by the proper quotient normalizer construction. -/
def IsConnectedReductive.rankOneNonidentityNormalizerOfProperFlagQuotient
    (hG : IsConnectedReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hconj : MaximalToriAreConjugate P)
    (hproper : SubgroupFunctor.range j ≠ ⊤)
    (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (n : ℕ) (ρ : MatrixRepresentation G (Fin (n + 1))) (l : Fin (n + 1))
    (hstab : ∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ G.X),
      x ∈ (SubgroupFunctor.range j).carrier V ↔
        ∃ c : Γ(V.left, ⊤)ˣ,
          (ρ.pointMatrix V x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(V.left, ⊤)) *ᵥ
              Pi.single l 1 =
            (c : Γ(V.left, ⊤)) • (Pi.single l (1 : Γ(V.left, ⊤)) :
              Fin (n + 1) → Γ(V.left, ⊤))) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  letI := hG.smooth
  letI := hG.connectedSpace
  let e := hG.rankOneRelativeWeylQuotientSignEmbedding_of_isMaximalTorus i hi hT hdep
  letI : Finite (relativeWeylGroup i) := Finite.of_injective e e.injective
  exact nonidentityNormalizerOfProperFlagQuotient i hi j hj f hf hc hconj hproper q
    hfib n ρ l hstab

end Langlands.GroupScheme
