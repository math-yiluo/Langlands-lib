import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicStandardSiegelFactors
import Langlands.Global.AdelicRepresentationHeight

/-! # Siegel sets, truncated Siegel sets and the functions `F^P(x, T)`

Arthur 2005, §8, pp.37–38, and §13, p.70; Arthur 1978, §6, pp.940–941. For a connected reductive
group `G` over a number field `F` with the data of `Langlands.Global.ArthurTruncation`:

* the Siegel set `S^P(T_1, ω) = {p a k : p ∈ ω, a ∈ A_0(ℝ)^0, k ∈ K, β(H_0(a) − T_1) > 0, β ∈ Δ_0^P}`,
  with `ω = Ω_N Ω_M ⊆ N_0(𝔸) M_0(𝔸)^1` compact, built as the published ordered factor product
  `AdelicSiegelFactors.productSet`;
* the truncated Siegel set `S^P(T_1, T, ω) = {x ∈ S^P(T_1, ω) : ϖ(H_0(x) − T) ≤ 0, ϖ ∈ Δ̂_0^P}`;
* the characteristic function `F^P(x, T)` of the projection of `S^P(T_1, T, ω)` to
  `P(F) \ G(𝔸)`;
* rapid decrease on Siegel sets (Arthur 2005, p.70). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

variable (F i) in
/-- The embedding of `A_0(ℝ)^0` in `G(𝔸)`: the published `positiveMap` for the torus `T` itself
(`T₀ = T`, `j = 𝟙`), defined on the intrinsic positive subgroup of `T(𝔸)`. -/
abbrev positiveTorusMap : PositiveRealTorus.intrinsicSubgroup F T →ₜ* AdelicGroupPoints F G :=
  positiveMap F G T i T (𝟙 T)

/-- The chamber `{a ∈ A_0(ℝ)^0 : β(H_0(a) − T_1) > 0 for every β ∈ Δ_0^P}` for the standard
parabolic subgroup with `Δ_0^P = SP`. -/
def siegelChamber (SP : Finset (characterLattice T)) (T₁ : V T) :
    Set (PositiveRealTorus.intrinsicSubgroup F T) :=
  {a | ∀ β ∈ SP, 0 < eval T β (height hi hK hρ (positiveTorusMap F i a) - T₁)}

/-- **The Siegel set** `S^P(T_1, ω) = ω A_0(ℝ)^0(T_1) K` (Arthur 2005, p.37; Arthur 1978, p.940)
for `Δ_0^P = SP`: the published ordered factor product `Ω_N Ω_M a K` of the compact factors `C`
(`ω = Ω_N Ω_M`, `Ω_N ⊆ N_0(𝔸)`, `Ω_M ⊆ M_0(𝔸)^1`; the compact subgroup `C.compactSubgroup`, which
the statements take equal to `K`) over the chamber `siegelChamber`. -/
def siegelSet
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (SP : Finset (characterLattice T)) (T₁ : V T) : Set (AdelicGroupPoints F G) :=
  productSet F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T)
    (siegelChamber hi hK hρ SP T₁)

/-- **The truncated Siegel set** `S^P(T_1, T, ω)` (Arthur 2005, p.37; Arthur 1978, p.941): the
points `x` of the Siegel set with `ϖ(H_0(x) − T) ≤ 0` for every `ϖ ∈ Δ̂_0^P`, the weights
`ϖ_β = ArthurRelative.weight … SP β`, `β ∈ SP`. -/
def truncatedSiegelSet
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (SP : Finset (characterLattice T)) (T₁ Tp : V T) : Set (AdelicGroupPoints F G) :=
  {x | x ∈ siegelSet hi hK hρ C SP T₁ ∧
    ∀ β ∈ SP, ArthurRelative.weight hG hi ν D (SP : Set (characterLattice T)) β
      (height hi hK hρ x - Tp) ≤ 0}

/-- **Arthur's `F^P(x, T)`** (Arthur 2005, p.37; Arthur 1978, p.941): `1` if `δx` lies in the
truncated Siegel set `S^P(T_1, T, ω)` for some `δ ∈ P(F)`, and `0` otherwise; that is, the
characteristic function of the projection of `S^P(T_1, T, ω)` to `P(F) \ G(𝔸)`, as a function on
`G(𝔸)`. -/
def siegelIndicator
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (SP : Finset (characterLattice T)) (T₁ Tp : V T) (x : AdelicGroupPoints F G) : ℤ :=
  if ∃ δ ∈ parabolicRationalImage (Standard.parabolicHom i ν (SP : Set (characterLattice T))),
      δ * x ∈ truncatedSiegelSet hG hi D hK hρ C SP T₁ Tp then 1 else 0

/-- **Rapid decrease** (Arthur 2005, p.70): for every Siegel set `S = S^G(T_1, ω)` with the
compact subgroup `K` and every `n`, there is `B` with `|φ(x)| ≤ B ‖x‖^{−n}` for
`x ∈ S ∩ G(𝔸)^1`. The height `‖x‖` is the published `RepresentationGrowth.adelicSourceNorm` of a
matrix representation `rho`. -/
def IsRapidlyDecreasing {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅),
    C.compactSubgroup = K → ∀ (T₁ : V T) (n : ℕ), ∃ B : ℝ,
      ∀ x ∈ siegelSet hi hK hρ C (simpleFinset ν hG hi) T₁, x ∈ normOneSubgroup F G →
        ‖φ x‖ ≤ B * RepresentationGrowth.adelicSourceNorm F G rho x ^ (-(n : ℝ))

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
theorem mem_siegelSet_iff
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (SP : Finset (characterLattice T)) (T₁ : V T) (x : AdelicGroupPoints F G) :
    x ∈ siegelSet hi hK hρ C SP T₁ ↔
      ∃ n ∈ C.omegaN, ∃ m ∈ C.omegaM, ∃ a : PositiveRealTorus.intrinsicSubgroup F T,
        (∀ β ∈ SP, 0 < eval T β (height hi hK hρ (positiveTorusMap F i a) - T₁)) ∧
        ∃ k ∈ C.compactSubgroup,
          map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
            map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
              positiveTorusMap F i a * k = x := by
  exact mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T (𝟙 T) _ x

end Langlands.Global.ArthurTruncation
