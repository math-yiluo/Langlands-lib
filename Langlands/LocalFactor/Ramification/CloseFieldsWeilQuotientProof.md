# Proof of the close-fields comparison of Weil quotients

Module `Langlands.LocalFactor.Ramification.CloseFieldsWeilQuotientProof`, namespace
`Langlands.Ramification.Local`.

`closeFieldsWeilQuotient : CloseFieldsWeilQuotientStatement.{u}` proves the Weil form of the
close-fields comparison (the page of `CloseFieldsStatement`): for a `p`-adic field `F` with absolute
ramification index `e`, residue field `k` and `X = k((t))`, there is an isomorphism of topological
groups `W_F/W_F^e ≃ W_X/W_X^e` between the quotients of the local Weil groups by their upper groups
at `e`, carrying the image of `W_F^v` onto the image of `W_X^v` for every `0 ≤ v ≤ e`, such that
classes that correspond have the same degree. No hypothesis is added: the residue-degree
compatibility it needs is proved (see `Wintenberger.Comparison` and `Wintenberger.Degree`).

## Other statements

For a topological group `Γ` with a degree `d : Γ →ₜ* Weil.ProfiniteIntegers` and a normal subgroup
`N ≤ ker d`:

- `quotientDegree d N hN : Γ ⧸ N →ₜ* Weil.ProfiniteIntegers`, the induced degree, with
  `quotientDegree_mk`.
- `pullbackQuotientHom d N hN : Weil.Pullback d →ₜ* Weil.Pullback (quotientDegree d N hN)`,
  `(g, n) ↦ (gN, n)`; it is surjective (`pullbackQuotientHom_surjective`), its kernel is
  `N.comap (Weil.projection d)` (`pullbackQuotientHom_ker`), and it is an open map
  (`pullbackQuotientHom_isOpenMap`).
- `pullbackQuotientEquiv d N hN : (Weil.Pullback d ⧸ N.comap (Weil.projection d).toMonoidHom) ≃ₜ*
  Weil.Pullback (quotientDegree d N hN)`, with `pullbackQuotientEquiv_mk`.

For degrees `d₁`, `d₂` on topological groups `Γ₁`, `Γ₂`:

- `pullbackCongr d₁ d₂ (φ : Γ₁ ≃ₜ* Γ₂) (h : ∀ g, d₂ (φ g) = d₁ g) : Weil.Pullback d₁ ≃ₜ*
  Weil.Pullback d₂`, `(g, n) ↦ (φ g, n)`, with `pullbackCongr_mem` and `pullbackCongr_apply`.
- `exists_weilQuotientIso d₁ d₂ F₁ F₂ x (hN₁ : F₁ x ≤ ker d₁) (hN₂ : F₂ x ≤ ker d₂)
  (φ : (Γ₁ ⧸ F₁ x) ≃ₜ* (Γ₂ ⧸ F₂ x)) (hdeg : ∀ g₁ g₂, φ (mk g₁) = mk g₂ → d₁ g₁ = d₂ g₂)
  (hanti₁) (hanti₂) (hφ : ∀ y, a₀ ≤ y → y ≤ x → ((F₁ y).map (mk' (F₁ x))).map φ =
  (F₂ y).map (mk' (F₂ x))) : ∃ ψ : (Weil.Pullback d₁ ⧸ (F₁ x).comap (Weil.projection d₁)) ≃ₜ*
  (Weil.Pullback d₂ ⧸ (F₂ x).comap (Weil.projection d₂)), (∀ y, a₀ ≤ y → y ≤ x → the image of
  (F₁ y).comap (Weil.projection d₁) goes onto the image of (F₂ y).comap (Weil.projection d₂)) ∧
  ∀ w w', ψ (mk' _ w) = mk' _ w' → Weil.degree d₁ w = Weil.degree d₂ w'`.

## Proof

`pullbackQuotientHom_ker`: an element `(g, n)` of the pullback with `g ∈ N` has
`frobenius n = d g = 1`, so `n = 0` by `Weil.frobenius_injective`. `pullbackQuotientHom_isOpenMap`:
an open set of the pullback is the trace of an open set `O` of `Γ × ℤ`, and its image is the trace
of the image of `O` under the open map `(g, n) ↦ (gN, n)`, because the degree is constant on the
cosets of `N`. The induced isomorphism of groups is then continuous and open.

`exists_weilQuotientIso`: `φ` preserves degrees, so it induces `pullbackCongr` between the pullbacks
of the induced degrees, and `ψ` is the composite of `pullbackQuotientEquiv` for `d₁`, this
isomorphism and the inverse of `pullbackQuotientEquiv` for `d₂`. Then `ψ (wN₁) = w'N₂` exactly when
`φ` sends the class of the Galois part of `w` to that of `w'` and the degrees of `w` and `w'` agree.
The filtrations correspond because `F_i x ≤ F_i y` for `y ≤ x`.

`closeFieldsWeilQuotient`: `exists_closeFieldsGaloisQuotient` (from `CloseFieldsGaloisQuotientProof`)
gives the Galois isomorphism with residue degrees and `G^e ≤ ker` on both sides, and
`exists_weilQuotientIso` applies with the Library's residue degrees
`Weil.Local.localResidueDegree F` and `Weil.Local.SepClosed.localResidueDegree X Ω`, the
filtrations `Padic.absoluteUpperRamificationGroup F` and `localAbsoluteUpperRamificationGroup X Ω`,
and `x = e`. The Library's Weil groups and upper groups are, by definition, the pullbacks of these
degrees and the preimages of these filtrations under the projections. The local normality
instances of the statement file (`padicWeilUpperGroup_normal`, `sepClosedWeilUpperGroup_normal`)
are installed locally. The main theorem carries `set_option maxHeartbeats 400000`.

## Declarations used

From the Library: `CloseFieldsWeilQuotientStatement`, `Weil.Pullback`, `Weil.pullbackSubgroup`,
`Weil.projection`, `Weil.degree`, `Weil.frobenius`, `Weil.frobenius_injective`,
`Weil.ProfiniteIntegers`, `Weil.Degree`, `Weil.Local.localResidueDegree`,
`Weil.Local.SepClosed.localResidueDegree`, `Padic.absoluteUpperRamificationGroup_antitone`,
`localAbsoluteUpperRamificationGroup_antitone`, `padicWeilUpperGroup_normal`,
`sepClosedWeilUpperGroup_normal`, `LocalField.Laurent.valuativeRel`. From
`CloseFieldsGaloisQuotientProof`: `exists_closeFieldsGaloisQuotient`. From Mathlib:
`QuotientGroup.lift`, `QuotientGroup.liftEquiv`, `QuotientGroup.isQuotientMap_mk`,
`QuotientGroup.isOpenMap_coe`, `IsOpenMap.prodMap`, `isOpen_induced_iff`,
`Equiv.toHomeomorphOfContinuousOpen`.

## Sources

Deligne, *Les corps locaux de caractéristique p, limites de corps locaux de caractéristique 0*, §3.5
(the comparison extends from Galois groups to Weil groups, the isomorphism of Galois quotients being
compatible with the residue degrees).
