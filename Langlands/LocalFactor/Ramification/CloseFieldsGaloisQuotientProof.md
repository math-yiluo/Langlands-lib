# Proof of the close-fields comparison of Galois quotients

Module `Langlands.LocalFactor.Ramification.CloseFieldsGaloisQuotientProof`, namespace
`Langlands.Ramification.Local`.

`closeFieldsGaloisQuotient : CloseFieldsGaloisQuotientStatement.{u}` proves the Galois form of the
close-fields comparison (the page of `CloseFieldsStatement`): for a `p`-adic field `F` with absolute
ramification index `e`, residue field `k` and `X = k((t))`, there is an isomorphism of topological
groups `G_F/G_F^e ≃ G_X/G_X^e` (with `G_X` the automorphisms of `SeparableClosure X`) carrying the
image of `G_F^v` onto the image of `G_X^v` for every `0 ≤ v ≤ e`.

The construction is stated with residue degrees in `exists_closeFieldsGaloisQuotient F`, which gives
an isomorphism `φ : G_F/G_F^e ≃ₜ* G_X/G_X^e` with the same filtration property, such that
`G_F^e ≤ ker (Weil.Local.localResidueDegree F)`, `G_X^e ≤ ker (Weil.Local.SepClosed.localResidueDegree
X Ω)`, and `φ (g₁ G_F^e) = g₂ G_X^e` implies that `g₁` and `g₂` have the same residue degree. It is
stated with the same `let` bindings as the statement (`X`, `Ω`, `e`, `upperK`, `upperX`) and is
used for the Weil form (`CloseFieldsWeilQuotientProof`).

## Other statements

- `exists_quotientIso_of_comap (ι : A →* G) (hι : Continuous ι) (FA : ℝ → Subgroup A)
  (FG : ℝ → Subgroup G) (ha₀ : a₀ ≤ x) [(FA x).Normal] [(FG x).Normal] [IsClosed (FG x : Set G)]
  (hanti : ∀ y ≤ x, FG x ≤ FG y) (hcomap : ∀ y, a₀ ≤ y → y ≤ x → (FG y).comap ι = FA y)
  (hsplit : ∀ g, ∃ a, ∃ n ∈ FG x, ι a * n = g) : ∃ φ : (A ⧸ FA x) ≃ₜ* (G ⧸ FG x), (∀ y, a₀ ≤ y →
  y ≤ x → ((FA y).map (QuotientGroup.mk' (FA x))).map φ.toMulEquiv.toMonoidHom =
  (FG y).map (QuotientGroup.mk' (FG x))) ∧ ∀ a, φ (QuotientGroup.mk a) = QuotientGroup.mk (ι a)`,
  for `A` compact and `G` a topological group: a homomorphism compatible with two filtrations and
  surjective modulo `F_G x` induces a filtered topological isomorphism of the quotients.
- `exists_kummerRootSystem F : ∃ ϖ πs, Kummer.IsKummerRootSystem F ϖ πs`: the canonical uniformizer
  of `F` (`TopologicalData.ord_uniformizer`) and successive `p`-th roots in the algebraic closure.
- `ramificationIndex_le_kummerBreak F : e ≤ Kummer.kummerBreak F = p e/(p − 1)`.

## Proof

Let `L = F(ϖ^{1/p^∞})` be the Kummer tower. By `Wintenberger.KummerTower` it is an infinite
arithmetically profinite extension, and `ψ_{L/F}` is the identity up to `p e/(p − 1)`; by the
Library's `Kummer.kummerTowerLimitUpperSup`, `G_L ⊔ G_F^v = G_F` for `v ≤ p e/(p − 1)`, in particular
for `v = 0` (total ramification) and `v = e`. `Wintenberger.normFieldComparison` gives an isomorphism
of topological groups `θ : Gal(F̄/L) ≃ Gal(X^sep/X)` with `θ(G_F^u ∩ G_L) = G_X^{ψ_{L/F}(u)}`, hence
`θ(G_F^v ∩ G_L) = G_X^v` for `-1 ≤ v ≤ e`.

Two applications of `exists_quotientIso_of_comap` follow, with `A = Gal(F̄/L)` and
`F_A y = G_F^y ∩ G_L`: first to the restriction `Gal(F̄/L) → G_F` (continuous by
`Wintenberger.continuous_restrictScalarsHom`; surjective modulo `G_F^e` because `G_L G_F^e = G_F`),
then to `θ`. The composite of the inverse of the first isomorphism with the second is the required
`G_F/G_F^e ≃ G_X/G_X^e`. This is Remark 4.1 (ii) of the plan note quoted on the statement's page:
`G_F/G_F^e ≃ G_L/(G_L ∩ G_F^e) ≃ G_X/G_X^e`.

Residue degrees: `normFieldComparison` also gives `d_F(a|_F) = d_X(θ a)` for `a ∈ Gal(F̄/L)`.
`G_F^e ≤ G_F^0`, which is the absolute inertia (`HerbrandBridge.absoluteUpperCanonicalInertia`), the
kernel of the residue degree (`Weil.Local.localResidueDegree_ker`); `G_X^e` is the image under `θ` of
`G_F^e ∩ G_L`, hence also in the kernel. If `φ (g₁ G_F^e) = g₂ G_X^e`, write `g₁ = a|_F · n` with
`n ∈ G_F^e`; then `g₂ ∈ θ(a) G_X^e`, and both have the degree of `a`. `exists_closeFieldsGaloisQuotient`
carries `set_option maxHeartbeats 1000000`.

## Declarations used

From the Library: `CloseFieldsGaloisQuotientStatement`, `Weil.Local.localResidueDegree`,
`Weil.Local.localResidueDegree_ker`, `Weil.Local.SepClosed.localResidueDegree`,
`HerbrandBridge.absoluteUpperCanonicalInertia`, `Padic.absoluteUpperRamificationGroup`,
`Padic.absoluteUpperRamificationGroup_antitone`, `Padic.absoluteUpperRamificationGroup_isClosed`,
`Padic.absoluteUpperRamificationGroup_normal`, `localAbsoluteUpperRamificationGroup_antitone`,
`localAbsoluteUpperRamificationGroup_isClosed`, `Kummer.kummerTower`, `Kummer.kummerBreak`,
`Kummer.kummerTowerLimitUpperSup`, `PadicField.TopologicalData.uniformizer`,
`PadicField.TopologicalData.ord_uniformizer`. From `Wintenberger`: `normFieldComparison`,
`wintenbergerPsi_eq_apfPsi`, `kummerTower_isAPF`, `kummerTower_not_finite`, `kummerTower_apfPsi`,
`kummerBreak_pos`, `isAPF_iff_isOpen`, `continuous_restrictScalarsHom`,
`padicField_isPerfectResidueLocalField`.

## Sources

Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*, §3.5
(the comparison of Galois quotients of close fields). Wintenberger 1983, Corollaires 3.2.3 and
3.3.6, applied to the Kummer tower `F(ϖ^{1/p^∞})`, which is arithmetically profinite (§1.4) with
`ψ_{L/F}` the identity up to `p e/(p − 1)`.
