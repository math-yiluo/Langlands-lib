import Langlands.Geometry.Building.DepthZero.Definitions
import Langlands.BruhatTits.IntegralModels.GeneralLinearIwahoriComparison

/-! # `GL_N` comparisons for the parahorics of KP building data

For a nonarchimedean local field `F`, `G = GL_N` over `F` and building data
`D : KPBuildingDatum G` satisfying the one-group axioms, these statements compare the facet
objects of `Langlands.Geometry.Building.DepthZero.Definitions` with the concrete subgroups
`K = GL_N(𝒪[F])` (the integral points of the standard model) and the standard Iwahori subgroup
`I` (`generalLinearIwahoriPoints`):

* `GeneralLinearVertexParahoricStatement`: the parahorics of the vertex facets are exactly
  the `G(F)`-conjugates of `K`;
* `GeneralLinearChamberParahoricStatement`: the parahorics of the chambers are exactly the
  `G(F)`-conjugates of `I`;
* `GeneralLinearVertexDepthZeroStatement`: at a vertex facet the neutral special fibre is
  connected reductive, the finite reductive quotient has `|GL_N(𝓀[F])|` elements, and
  `P_x / P_{x,0+}` is `GL_N(𝓀[F])` through any conjugation `P_x = g K g⁻¹` and reduction;
* `GeneralLinearChamberDepthZeroStatement`: at a chamber the finite reductive quotient has
  `(q - 1)^N` elements, `P_C / P_{C,0+}` is `(𝓀[F]ˣ)^N` through any conjugation `P_C = g I g⁻¹`
  and the diagonal of the reduction, and for `N ≥ 2` the neutral special fibre is not reductive;
* `GeneralLinearVertexStabilizerStatement`: the parahoric of a vertex `y` is the compact
  stabilizer `G(F)^1 ∩ G(F)_y`, and for `N ≥ 1` it is strictly smaller than `G(F)_y`.

The conjugate `g Q g⁻¹` of a subgroup `Q` is written `Q.map (MulAut.conj g).toMonoidHom`.
These definitions state the comparisons and do not prove them.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

/-- **Vertex parahorics of `GL_N` are the conjugates of `GL_N(𝒪[F])`.** For building data `D`
of `G = GL_N` over `F` satisfying the one-group axioms, the parahoric `D.parahoric x` of every
vertex facet `x = {y}` of the reduced building is `g K g⁻¹` for some `g ∈ G(F)`, where
`K = GL_N(𝒪[F])` is the group of integral points of the standard model; and every
`G(F)`-conjugate of `K` is the parahoric of a vertex facet (KP §15.1, 15.1.33). -/
def GeneralLinearVertexParahoricStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms →
      let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
      (∀ x : BuildingFacet D.base.toValuationBuildingData,
          (∃ y, D.base.IsVertex y ∧ x.val = {y}) →
            ∃ g, D.parahoric x = K.map (MulAut.conj g).toMonoidHom) ∧
        ∀ g, ∃ x : BuildingFacet D.base.toValuationBuildingData,
          (∃ y, D.base.IsVertex y ∧ x.val = {y}) ∧
            D.parahoric x = K.map (MulAut.conj g).toMonoidHom

/-- **Chamber parahorics of `GL_N` are the conjugates of the standard Iwahori subgroup.** For
building data `D` of `G = GL_N` over `F` satisfying the one-group axioms, the parahoric
`D.parahoric C` of every chamber `C` of the reduced building is `g I g⁻¹` for some `g ∈ G(F)`,
where `I = generalLinearIwahoriPoints F N` is the preimage in `GL_N(𝒪[F])` of the upper
triangular group of `GL_N(𝓀[F])`; and every `G(F)`-conjugate of `I` is the parahoric of a
chamber (KP Definition 7.4.5, §15.1, 15.1.33). -/
def GeneralLinearChamberParahoricStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms →
      let I := generalLinearIwahoriPoints F N
      (∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
          ∃ g, D.parahoric C = I.map (MulAut.conj g).toMonoidHom) ∧
        ∀ g, ∃ C : BuildingFacet D.base.toValuationBuildingData,
          D.base.IsChamber C.val ∧ D.parahoric C = I.map (MulAut.conj g).toMonoidHom

/-- **Depth zero at a vertex of `GL_N` (hyperspecial).** For building data `D` of `GL_N` over
`F` satisfying the one-group axioms and every vertex facet `x`:

* the special fibre of the neutral facet model is connected reductive;
* the finite reductive quotient `Ḡ_x(𝓀[F])` has `∏_{i < N} (q ^ N - q ^ i)` elements, where
  `q = |𝓀[F]|`;
* for every `g ∈ G(F)` with `P_x = g K g⁻¹`, `K = GL_N(𝒪[F])`, the radical preimage `P_{x,0+}` is
  normal in `P_x` and there is an isomorphism `P_x / P_{x,0+} ≃ GL_N(𝓀[F])` sending the class of
  `p` to the reduction of the integral matrix `g⁻¹ p g`
(KP Proposition 8.4.14, §13.2.6, 15.1.33). -/
def GeneralLinearVertexDepthZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
    (hD : D.SatisfiesGroupAxioms),
      let K := (GeneralLinear.standardIntegralModel 𝒪[F] F (Fin N)).integralPoints
      let q := Nat.card 𝓀[F]
      ∀ x : BuildingFacet D.base.toValuationBuildingData,
        (∃ y, D.base.IsVertex y ∧ x.val = {y}) →
          IsConnectedReductive (D.models.facetModels.model x).neutral.specialFibre ∧
          Nat.card (D.finiteReductiveQuotientGroup x hD) = ∏ i : Fin N, (q ^ N - q ^ (i : ℕ)) ∧
          ∀ g, D.parahoric x = K.map (MulAut.conj g).toMonoidHom →
            ∃ hN : (D.parahoricRadical x).Normal,
              letI : (D.parahoricRadical x).Normal := hN
              ∃ e : D.parahoric x ⧸ D.parahoricRadical x ≃* GL (Fin N) 𝓀[F],
                ∀ (p : D.parahoric x) (u : GL (Fin N) 𝒪[F]),
                  GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
                      (g⁻¹ * (p : rationalPoints _) * g) = glIntegralInclusion F N u →
                    e (p : D.parahoric x ⧸ D.parahoricRadical x) = glResidueMap F N u

/-- **Depth zero at a chamber of `GL_N` (Iwahori; not hyperspecial for `N ≥ 2`).** For
building data `D` of
`GL_N` over `F` satisfying the one-group axioms and every chamber `C`:

* the finite reductive quotient `Ḡ_C(𝓀[F])` has `(q - 1) ^ N` elements, where `q = |𝓀[F]|`;
* for every `g ∈ G(F)` with `P_C = g I g⁻¹`, `I = generalLinearIwahoriPoints F N`, the radical
  preimage `P_{C,0+}` is normal in `P_C` and there is an isomorphism
  `P_C / P_{C,0+} ≃ (𝓀[F]ˣ)^N` whose `i`-th coordinate on the class of `p` is the residue of the
  `i`-th diagonal entry of the integral matrix `g⁻¹ p g`;
* for `N ≥ 2` the special fibre of the neutral facet model is not connected reductive; since it
  is connected, it is not reductive
(KP Proposition 8.4.14, §13.2.6, 15.1.33). -/
def GeneralLinearChamberDepthZeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)))
    (hD : D.SatisfiesGroupAxioms),
      let I := generalLinearIwahoriPoints F N
      let q := Nat.card 𝓀[F]
      ∀ C : BuildingFacet D.base.toValuationBuildingData, D.base.IsChamber C.val →
        Nat.card (D.finiteReductiveQuotientGroup C hD) = (q - 1) ^ N ∧
        (∀ g, D.parahoric C = I.map (MulAut.conj g).toMonoidHom →
          ∃ hN : (D.parahoricRadical C).Normal,
            letI : (D.parahoricRadical C).Normal := hN
            ∃ e : D.parahoric C ⧸ D.parahoricRadical C ≃* (Fin N → 𝓀[F]ˣ),
              ∀ (p : D.parahoric C) (u : GL (Fin N) 𝒪[F]),
                GeneralLinear.rationalPointsEquiv N (CommRingCat.of F)
                    (g⁻¹ * (p : rationalPoints _) * g) = glIntegralInclusion F N u →
                  ∀ i : Fin N,
                    ((e (p : D.parahoric C ⧸ D.parahoricRadical C) i : 𝓀[F]ˣ) : 𝓀[F]) =
                      IsLocalRing.residue 𝒪[F] ((u : Matrix (Fin N) (Fin N) 𝒪[F]) i i)) ∧
        (2 ≤ N → ¬ IsConnectedReductive (D.models.facetModels.model C).neutral.specialFibre)

/-- **Vertex parahorics of `GL_N` are compact stabilizers but not full stabilizers.** For
building data `D` of `GL_N` over `F` satisfying the one-group axioms, a vertex `y` of the reduced
building and the facet `x` containing `y`, the parahoric `D.parahoric x` is the compact
stabilizer `G(F)^1 ∩ G(F)_y`, and for `N ≥ 1` it is a proper subgroup of the full stabilizer
`G(F)_y` (KP Theorem 4.2.15, 15.1.33). -/
def GeneralLinearVertexStabilizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ)
    (D : KPBuildingDatum (GeneralLinear.groupScheme (Fin N) (CommRingCat.of F))),
    D.SatisfiesGroupAxioms →
      ∀ y, D.base.IsVertex y →
        ∀ x : BuildingFacet D.base.toValuationBuildingData, y ∈ x.val →
          D.parahoric x = D.base.compactStabilizer y ∧
            (1 ≤ N → D.parahoric x < D.base.fixer y)

end Langlands.Geometry.Building
