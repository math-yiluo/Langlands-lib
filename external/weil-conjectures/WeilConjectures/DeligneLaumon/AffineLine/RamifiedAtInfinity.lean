/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapCongr
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStrictlyHenselian
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection
public import WeilConjectures.WeilSheaf.ArtinSchreierTrivialization

/-!
# Linear Artin–Schreier sheaves are ramified at infinity

Let `k̄` be an algebraic closure of `k₀`, `K = k̄((t))` and `t = 1 / x` the coordinate at
`∞ ∈ ℙ¹`. We compare two pullbacks to the punctured formal disc `Spec K` at infinity, along the
generic point `x = 1 / t` of a dense open `Ū ⊆ 𝔸¹_{k̄}`.

* A lisse Weil sheaf `F` on `U₀` which is unramified at infinity becomes constant on `Spec K`:
  it extends to a lisse sheaf `G` on a neighbourhood `W` of `∞`, and the point `x = 1 / t`
  extends to the point `z = t` of `W̄` with values in the strictly henselian ring `k̄⟦t⟧`, on
  which `G` is constant
  (`AlgebraicGeometry.WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity`).
* The geometric linear Artin–Schreier sheaf `ℒ_{ψ(a x)}`, `a ≠ 0`, is not a subquotient of a
  constant sheaf on `Spec K`: over an algebraic closure `L` of `K` the Artin–Schreier cover
  `u^q - u = a / t` acquires a point, on which every deck transformation `σ̄_c` is induced by a
  `K`-automorphism of `L`, an element of the inertia group at `∞`; and `σ̄_c` acts on the
  trivialised `ĀS^* ℒ_ψ` by `ψ(-c)`
  (`AlgebraicGeometry.affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage`).

Together they give the blueprint lemma `lemma-unramified-at-infinity-no-linear-characters--1`: a
nonzero linear Artin–Schreier sheaf is not unramified at infinity
(`AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier`), and the case `a ≠ 0` of
`lemma-unramified-at-infinity-no-linear-characters`: a lisse sheaf unramified at infinity has no
geometric constituent `ℒ_{ψ(a x)}|_U` with `a ≠ 0`
(`WeilSheaf.LisseOnDenseOpen.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity'`).
The second statement needs no semisimplicity: a subquotient of a constant sheaf on `Spec K` is
already excluded.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity`
- `AlgebraicGeometry.affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage`
- `AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier`
- `WeilSheaf.LisseOnDenseOpen.not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity'`
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "K̄" => LaurentSeries (AlgebraicClosure k₀)

/-- The pullback along a composite, for a morphism equal to the composite. -/
noncomputable def ProEtale.adicUpperStarCompObjIso {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (e : f ≫ g = h) (F : ProEtale.AdicSheaf l Z) :
    (f)^*ᵃ[l].obj ((g)^*ᵃ[l].obj F) ≅ (h)^*ᵃ[l].obj F :=
  ((ProEtale.adicUpperStarComp l f g).app F).symm ≪≫ (ProEtale.adicUpperStarCongr l e).app F

namespace affineLine

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- **`ℒ_{ψ(a x)}` is not a subquotient of a constant sheaf on the punctured disc at `∞`.** For
`ψ ≠ 1` and `a ≠ 0` in `k̄`, the pullback of `ℒ_ψ` along the point `x = a / t` of `𝔸¹_{k̄}`
with values in `K = k̄((t))` is not a quotient of a subsheaf of a constant sheaf `ℚ̄_ℓⁿ`: the
inertia group at infinity acts on it through the nontrivial character `ψ`. -/
theorem not_epi_upperStar_laurentPoint_artinSchreierImage (hψ : ψ ≠ 1)
    {a : AlgebraicClosure k₀} (ha : a ≠ 0) {n : ℕ} {B : ProEtale.AdicSheaf l (Spec (.of K̄))}
    (m : B ⟶ ⨁ fun _ : Fin n ↦ ProEtale.AdicSheaf.unit l (Spec (.of K̄))) [Mono m]
    (p : B ⟶ (laurentPoint k₀ a)^*ᵃ[l].obj (artinSchreierImage l ψ)) [Epi p] : False := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, ψ c₀ ≠ 1 := by
    by_contra! h
    exact hψ (DFunLike.ext _ _ fun x ↦ by rw [h x, AddChar.one_apply])
  obtain ⟨z', hz', hσ⟩ := exists_comp_geometricArtinSchreierMap_eq_laurentPoint k₀ ha
  obtain ⟨σ, hσπ, hσz⟩ := hσ (-c₀)
  exact ProEtale.not_epi_of_mono_biproduct_unit_of_twist hσπ
    (geometricTranslation_comp_artinSchreierMap k₀ (-c₀)) hz' hσz
    (artinSchreierTrivialization l ψ) (by rwa [neg_neg]) (germ_artinSchreierTrivialization ψ _)
    m p

end affineLine

namespace WeilSheaf

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]

/-- **A sheaf unramified at infinity is constant on the punctured disc at `∞`.** If the lisse
Weil sheaf `F` on `U₀ ⊆ 𝔸¹` extends to a lisse sheaf on a neighbourhood `W` of `∞`, its
underlying sheaf becomes constant after pullback along any lift `Spec k̄((t)) ⟶ Ū` of the point
`x = 1 / t`: this point extends to the point `z = t` of `W̄` with values in the strictly
henselian ring `k̄⟦t⟧`, on whose spectrum lisse sheaves are constant. -/
theorem exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity {F : WeilSheaf k₀ l U}
    {j : U ⟶ affineLine k₀} [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hF : F.IsUnramifiedAtInfinity j)
    (zU : Spec (.of K̄) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hzU : zU ≫ Scheme.Hom.geometricFiberMap j (comp_over j _) = laurentPoint k₀ 1) :
    ∃ n : ℕ, Nonempty ((zU)^*ᵃ[l].obj F.obj.carrier ≅
      ⨁ fun _ : Fin n ↦ ProEtale.AdicSheaf.unit l (Spec (.of K̄))) := by
  obtain ⟨W, hW, hcov, G, hG, ⟨e⟩⟩ := hF
  set ι := ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))
  have hrange : Set.range (j ≫ ι) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hW ▸ j.mem_opensRange.2 ⟨x, rfl⟩ : j x ∈ ι ⁻¹ᵁ W)
  set j' := IsOpenImmersion.lift W.ι (j ≫ ι) hrange
  have hj' : j' ≫ W.ι = j ≫ ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨zW, hzW⟩ := exists_comp_geometricFiberMap_eq_powerSeriesInfinityPoint k₀ W hcov
  -- the point `x = 1 / t` of `Ū` is the restriction of the point `z = t` of `W̄`
  set ρ := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries (AlgebraicClosure k₀)) K̄))
  have hsq : zU ≫ Scheme.Hom.geometricFiberMap j' (comp_over j' _) = ρ ≫ zW := by
    rw [← cancel_mono (Scheme.Hom.geometricFiberMap W.ι (comp_over W.ι _)), Category.assoc,
      Category.assoc, hzW, ← laurentPoint_one_comp_geometricFiberMap_affineChart, ← hzU,
      Category.assoc, ← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
    exact congrArg _ (Scheme.Hom.geometricFiberMap_congr hj' _ _)
  -- `G` is constant on `Spec k̄⟦t⟧`
  obtain ⟨n, ⟨eW⟩⟩ := ProEtale.IsAdicLisseSheaf.exists_iso_biproduct_unit_of_isStrictlyHenselian
    (ProEtale.IsAdicLisseSheaf.upperStar zW hG)
  refine ⟨n, ⟨(zU)^*ᵃ[l].mapIso
      ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).mapIso e).symm ≪≫
    ProEtale.adicUpperStarCompObjIso hsq _ ≪≫
    (ProEtale.adicUpperStarCompObjIso rfl _).symm ≪≫ (ρ)^*ᵃ[l].mapIso eW ≪≫
      Functor.mapBiproduct _ _ ≪≫ biproduct.mapIso fun _ ↦ ProEtale.adicUpperStarUnitIso l _⟩⟩

end WeilSheaf

variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- **Linear Artin–Schreier sheaves are ramified at infinity.** For a nontrivial additive
character `ψ` and `a ≠ 0`, the Artin–Schreier sheaf `ℒ_{ψ(a x)}` on `𝔸¹_{k₀}` does not extend
to a lisse sheaf on a neighbourhood of `∞` in `ℙ¹`: otherwise it would be constant on the
punctured disc at `∞`
(`AlgebraicGeometry.WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity`),
while the inertia group at `∞` acts on it through `ψ`.
(blueprint: `lemma-unramified-at-infinity-no-linear-characters--1`) -/
theorem not_isUnramifiedAtInfinity_artinSchreier (hψ : ψ ≠ 1) {a : k₀} (ha : a ≠ 0) :
    ¬ (artinSchreier ψ a).IsUnramifiedAtInfinity (𝟙 (affineLine k₀)) := by
  intro h
  obtain ⟨n, ⟨e⟩⟩ := WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity h
    (laurentPoint k₀ 1) (by
      rw [Scheme.Hom.geometricFiberMap_id, Category.comp_id])
  have hb : algebraMap k₀ (AlgebraicClosure k₀) a * 1 ≠ 0 := by simpa using ha
  exact affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage ψ hψ hb e.hom
    ((ProEtale.adicUpperStarCompObjIso (laurentPoint_comp_geometricFiberMap_smul k₀ a 1) _).hom ≫
      (laurentPoint k₀ _)^*ᵃ[l].map (affineLine.artinSchreierCarrierIso ψ).hom)

namespace WeilSheaf.LisseOnDenseOpen

variable (D : LisseOnDenseOpen k₀ l)

/-- A lisse sheaf unramified at infinity has no geometric constituent `ℒ_{ψ(a x)}|_U` with
`a ≠ 0`: on the punctured disc at `∞` the sheaf becomes constant
(`AlgebraicGeometry.WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity`),
so a geometric constituent becomes a subquotient of a constant sheaf, which `ℒ_{ψ(a x)}` is not
(`AlgebraicGeometry.affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage`).
(blueprint: `lemma-unramified-at-infinity-no-linear-characters`, case `a ≠ 0`) -/
theorem not_hasLinearArtinSchreierConstituent_of_isUnramifiedAtInfinity' (hψ : ψ ≠ 1)
    (hinf : D.IsUnramifiedAtInfinity) {a : AlgebraicClosure k₀} (ha : a ≠ 0) :
    ¬ D.sheaf.HasLinearArtinSchreierConstituent ψ a D.j := by
  rintro ⟨B, i, p, -, hi, hp⟩
  have : Nonempty (affineLine k₀) :=
    ⟨(laurentPoint k₀ 1 ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)
      (IsLocalRing.closedPoint K̄)⟩
  have : Nonempty D.U := D.j.denseRange.nonempty
  obtain ⟨zU, hzU⟩ := exists_comp_geometricFiberMap_eq_laurentPoint k₀ D.j
  obtain ⟨n, ⟨e⟩⟩ :=
    WeilSheaf.exists_iso_upperStar_biproduct_unit_of_isUnramifiedAtInfinity hinf zU hzU
  have hpt : (zU ≫ Scheme.Hom.geometricFiberMap D.j (comp_over D.j _) ≫
      affineLine.geometricSMul k₀ a) ≫
        Scheme.Hom.geometricFiberMap (affineLine.smul k₀ 1) (comp_over _ _) =
      laurentPoint k₀ (algebraMap k₀ (AlgebraicClosure k₀) 1 * (a * 1)) := by
    rw [Category.assoc, Category.assoc, reassoc_of% hzU,
      reassoc_of% laurentPoint_comp_geometricSMul,
      laurentPoint_comp_geometricFiberMap_smul]
  have hb : algebraMap k₀ (AlgebraicClosure k₀) 1 * (a * 1) ≠ 0 := by simpa using ha
  exact affineLine.not_epi_upperStar_laurentPoint_artinSchreierImage ψ hψ hb
    ((zU)^*ᵃ[l].map i ≫ e.hom)
    ((zU)^*ᵃ[l].map p ≫ (zU)^*ᵃ[l].map (ProEtale.adicUpperStarCompObjIso rfl _).hom ≫
      (ProEtale.adicUpperStarCompObjIso rfl _).hom ≫
      (ProEtale.adicUpperStarCompObjIso hpt _).hom ≫
      (laurentPoint k₀ _)^*ᵃ[l].map (affineLine.artinSchreierCarrierIso ψ).hom)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
