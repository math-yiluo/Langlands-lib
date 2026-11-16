import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement

/-! # Consequences of rank-one normalization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Over a local ring, the coordinate pairing of a root with a coroot of a fibrewise root
datum is the root-datum pairing. -/
theorem coPairing_root_coroot [IsLocalRing R] (hP : IsFibrewiseRootDatumOf I G i P)
    (β a : J) : coPairing (P.root β) (P.coroot a) = P.pairingIn ℤ β a := by
  have h := hP.pairing (IsLocalRing.ResidueField R) (P.root β) (P.coroot a)
  rw [coPairing, ← h, RootPairing.root_coroot_eq_pairing, ← P.algebraMap_pairingIn ℤ]
  simp

/-- **The action of `N²` on root groups.** If a global point `N` has square `a^∨(-1)`, then
conjugation by `N²` acts on every root parametrization `w` of a root `β` by the sign
`(-1)^⟨β, a^∨⟩`. -/
theorem conj_sq_rootPoint [IsLocalRing R] (hP : IsFibrewiseRootDatumOf I G i P) {a : J}
    {N : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X}
    (hN : N * N = cocharPoint (P.coroot a) (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1) ≫
      i.hom.hom)
    {β : J} {w : Ga R ⟶ G} (hw : IsRootParametrization i (P.root β) w)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    (G.constantPoint N Z * G.constantPoint N Z) * rootPoint w Z x *
        (G.constantPoint N Z * G.constantPoint N Z)⁻¹ =
      rootPoint w Z ((P.pairingIn ℤ β a).negOnePow • x) := by
  rw [← GroupScheme.constantPoint_mul, hN, ← toUnit_comp_eq_constantPoint, ← Category.assoc,
    hw.equivariant]
  congr 1
  have hval := torusChar_cocharPoint (R := R) (P.root β) (P.coroot a)
    (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1)
  rw [coPairing_root_coroot hP] at hval
  unfold torusChar at hval
  rw [VectorGroup.charValue_comp, hval]
  rcases Int.even_or_odd (P.pairingIn ℤ β a) with he | ho
  · rw [he.neg_one_zpow, Int.negOnePow_even _ he, Units.val_one, map_one, one_mul, one_smul]
  · rw [ho.neg_one_zpow, Int.negOnePow_odd _ ho, Units.val_neg, Units.val_one, map_neg,
      map_one, neg_one_mul, Units.neg_smul, one_smul]

end LocalSplitCell

end Langlands.GroupScheme
