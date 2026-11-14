import Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements
import Langlands.Representation.Exponents.ArbitraryParabolic
import Langlands.Representation.Jacquet.CompressedImageLift
import Langlands.Representation.Smooth.Definitions

/-! # Renard VI.6.1 Proposition and VI.9.1 Proposition along an arbitrary parabolic

Statements only. Renard 2026, VI.6.1 (printed pp.176–177 / PDF pp.182–183) and VI.9.1
(printed pp.195–197 / PDF pp.201–203), with the notion of Iwahori decomposition of V.5.2 (ii)
(printed p.123 / PDF p.129). The parabolic data are those of the published
`GeneralizedJacquetContractingRangeStatement`: actual rational parabolics `P = MN` and
`P̄ = M N̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`, and a split component `a : A → M`
with a compatible root presentation of `P` and restricted simple roots `Δ(P)`. For `ε > 0`,
`A^+(ε) = {t ∈ A(F) | |α(t)|_F < ε for α ∈ Δ(P)}`.

* `RepresentedChamberIwahoriContractionStatement` (derived): for every compact open `K`
  with an Iwahori decomposition `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))` there is
  `0 < ε ≤ 1` such that `A^+(ε)` is nonempty and the image in `G(F)` of every
  `t ∈ A^+(ε)` satisfies the Iwahori contraction conditions `Jacquet.IsIwahoriContraction`.
* `RepresentedCanonicalSectionStatement`: VI.6.1, (VI.6.1.2) and Proposition, for such `K`
  and every admissible complex representation.
* `RepresentedUniformCompressionStabilizationStatement`: VI.9.1 Proposition, with the
  conclusion drawn from it in the proof of the VI.9.1 Theorem, for every `M`-central
  element satisfying the Iwahori contraction conditions.
* `RepresentedGeneralizedJacquetRemarksStatement`: the bound `b ≤ c(G, K)` and Remarks 1–2
  of VI.9.1, in the same setting.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Derived from Renard V.5.2 and the proofs of VI.6.1 and VI.9.1 ("On choisit alors
`t ∈ C_A^{++}`"; "il existe `ε > 0` tel que pour tout `t ∈ C_A^+(ε)`, `Γ ⊂ t⁻¹ K_N t`").
For actual rational parabolics `P = MN` and `P̄ = M N̄` with the same Levi and
`P(F) ∩ P̄(F) = M(F)`, every compact open `K` with `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`,
and every split component `a : A → M` with a compatible root presentation of `P` and
restricted simple roots `Δ(P)`, there is `0 < ε ≤ 1` such that `A^+(ε)` is nonempty and,
for every `t ∈ A^+(ε)`, the image of `t` in `G(F)` satisfies
`Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F)`. -/
def RepresentedChamberIwahoriContractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
        (∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
          ∃ y ∈ K.toSubgroup ⊓ pointImage (m ≫ p),
            ∃ z ∈ K.toSubgroup ⊓ pointImage (n ≫ p), x = l * y * z) →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
          (pres : ParabolicRootPresentation p m a),
          let Δ : Set (characterLattice A) :=
            (fun α => pres.data.f ≫ α) ''
              (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
          let incG : rationalPoints A.toGrp →* rationalPoints G :=
            rationalPoints.map (a ≫ m ≫ p)
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
            (∃ t : rationalPoints A.toGrp,
              ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) ∧
            ∀ t : rationalPoints A.toGrp,
              (∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) →
              Jacquet.IsIwahoriContraction K (pointImage (n ≫ p)) (pointImage (m ≫ p))
                (pointImage (nbar ≫ pbar)) (incG t)

/-- Renard VI.6.1, (VI.6.1.2) and Proposition, for an arbitrary actual rational parabolic
and every compact open subgroup `K` with an Iwahori decomposition
`K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`. Let `a : A → M` be a split component with a
compatible root presentation of `P` and restricted simple roots `Δ(P)`. For every
admissible complex representation `V` there are `0 < ε ≤ 1` and a section `s` of the
Jacquet map `j : V^K → (V_N)^{K ∩ M(F)}` such that `A^+(ε)` is nonempty and, for every
`t ∈ A^+(ε)` with image `t` in `G(F)`, `ker j ⊆ ker π(a_{t,K})` (VI.6.1.2),
`ker j = ker π(a_{t,K})`, `V^K = ker π(a_{t,K}) ⊕ Im π(a_{t,K})`, `j` maps
`Im π(a_{t,K})` bijectively onto `(V_N)^{K ∩ M(F)}`, `Im π(a_{t,K})` is the stable image
and `ker j` the kernel supremum of the compressed action of `t`, and `s` is the inverse of
this bijection; so the decomposition and the section do not depend on `t`. Here
`π(a_{t,K})` is the compressed action `v ↦ e_K(π(t) v)` on `V^K`. -/
def RepresentedCanonicalSectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))),
        (∀ x ∈ K, ∃ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
          ∃ y ∈ K.toSubgroup ⊓ pointImage (m ≫ p),
            ∃ z ∈ K.toSubgroup ⊓ pointImage (n ≫ p), x = l * y * z) →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
          (pres : ParabolicRootPresentation p m a),
          let Δ : Set (characterLattice A) :=
            (fun α => pres.data.f ≫ α) ''
              (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
          let incG : rationalPoints A.toGrp →* rationalPoints G :=
            rationalPoints.map (a ≫ m ≫ p)
          let Nf := pointImage (n ≫ p)
          let Mf := pointImage (m ≫ p)
          let hMN : Mf ≤ Subgroup.normalizer (Nf : Set (rationalPoints G)) :=
            pointImage_le_normalizer p m n hn
          ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
            (ρ : Representation ℂ (rationalPoints G) V) (hρ : Langlands.IsAdmissible ρ),
            let j := Jacquet.fixedJacquetMap ρ Nf Mf hMN K.toSubgroup
            ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
              (∃ t : rationalPoints A.toGrp,
                ∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) ∧
              ∃ s : fixedVectors (Jacquet.action ρ Nf Mf hMN)
                  (K.toSubgroup.comap Mf.subtype) →ₗ[ℂ] fixedVectors ρ K.toSubgroup,
                j.comp s = LinearMap.id ∧
                ∀ t : rationalPoints A.toGrp,
                  (∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) →
                  let C := Jacquet.compressedAction ρ hρ.1 K hK (incG t)
                  LinearMap.ker j ≤ LinearMap.ker C ∧
                  LinearMap.ker C = LinearMap.ker j ∧
                  IsCompl (LinearMap.ker C) (LinearMap.range C) ∧
                  Function.Bijective
                    (Jacquet.compressedImageJacquetMap ρ hρ.1 K hK (incG t) Nf Mf hMN) ∧
                  LinearMap.range C = Jacquet.stableImage ρ hρ.1 K hK (incG t) ∧
                  Jacquet.powerKernelSup ρ hρ.1 K hK (incG t) = LinearMap.ker j ∧
                  LinearMap.range s = LinearMap.range C ∧
                  ∀ hb : Function.Bijective
                      (Jacquet.compressedImageJacquetMap ρ hρ.1 K hK (incG t) Nf Mf hMN),
                    Jacquet.compressedImageLift ρ hρ.1 K hK (incG t) Nf Mf hMN hb = s

/-- Renard VI.9.1, Proposition, for an arbitrary actual rational parabolic, together with
the conclusion drawn from it in the proof of the VI.9.1 Theorem. For actual rational
parabolics `P = MN` and `P̄ = M N̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`, every
compact open `K` and every `M(F)`-central `g` satisfying the Iwahori contraction conditions
for `(N(F), M(F), N̄(F))`, write `A` for the compressed action `v ↦ e_K(π(g) v)` on `V^K`.
There is one exponent `b` such that, for every smooth complex representation on a carrier in
`Type v`: every power of `A` of exponent at least `b` has range the stable image `V^K_*` and
kernel the kernel supremum `V^K_0`; `V^K = V^K_0 ⊕ V^K_*`; the kernel of the Jacquet map
`j : V^K → (V_N)^{K ∩ M(F)}` is `V^K_0`; and `j` maps `V^K_*` bijectively onto
`(V_N)^{K ∩ M(F)}`. -/
def RepresentedUniformCompressionStabilizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      let Nf := pointImage (n ≫ p)
      let Mf := pointImage (m ≫ p)
      let Nbarf := pointImage (nbar ≫ pbar)
      let hMN : Mf ≤ Subgroup.normalizer (Nf : Set (rationalPoints G)) :=
        pointImage_le_normalizer p m n hn
      ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
        (g : rationalPoints G),
        (∀ x ∈ Mf, x * g = g * x) →
        Jacquet.IsIwahoriContraction K Nf Mf Nbarf g →
        ∃ b : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
          (∀ s : ℕ, b ≤ s →
            Jacquet.stableImage ρ hρ K hK g =
                LinearMap.range (Jacquet.compressedAction ρ hρ K hK g ^ s) ∧
              Jacquet.powerKernelSup ρ hρ K hK g =
                LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g ^ s)) ∧
          Jacquet.CompactCompressionSplits ρ hρ K hK g ∧
          LinearMap.ker (Jacquet.fixedJacquetMap ρ Nf Mf hMN K.toSubgroup) =
            Jacquet.powerKernelSup ρ hρ K hK g ∧
          Function.Bijective (Jacquet.stableImageJacquetMap ρ hρ K hK g Nf Mf hMN)

/-- Renard VI.9.1, the bound on `b` in the Proposition and Remarks 1–2, for an arbitrary
actual rational parabolic. Same data as `RepresentedUniformCompressionStabilizationStatement`;
write `A` for the compressed action of `g` on `V^K`, `V^K_0` for its kernel supremum and
`V^K_*` for its stable image. Then:

* (bound) for every `c` bounding `dim V^K` over the irreducible smooth representations,
  every power of `A` of exponent at least `c` has kernel `V^K_0` and range `V^K_*`, for
  every smooth representation;
* (Remark 1) every other `M(F)`-central `g'` satisfying the same conditions gives the same
  `V^K_0` and `V^K_*`;
* (Remark 2) there are compact open subgroups `C` of `N(F)` and `C̄` of `N̄(F)` such that,
  for every smooth representation, `V^K_0` is the kernel of the average `e_C` on `V^K` and
  `V^K_*` is the image of `e_K ∘ e_{C̄}`. -/
def RepresentedGeneralizedJacquetRemarksStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      let Nf := pointImage (n ≫ p)
      let Mf := pointImage (m ≫ p)
      let Nbarf := pointImage (nbar ≫ pbar)
      ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
        (g : rationalPoints G),
        (∀ x ∈ Mf, x * g = g * x) →
        Jacquet.IsIwahoriContraction K Nf Mf Nbarf g →
        -- the bound `b ≤ c(G, K)`
        (∀ c : ℕ,
          (∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), A.IsIrreducible →
            Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c) →
          ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
            (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
            ∀ s : ℕ, c ≤ s →
              Jacquet.stableImage ρ hρ K hK g =
                  LinearMap.range (Jacquet.compressedAction ρ hρ K hK g ^ s) ∧
                Jacquet.powerKernelSup ρ hρ K hK g =
                  LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g ^ s)) ∧
        -- Remark 1
        (∀ g' : rationalPoints G, (∀ x ∈ Mf, x * g' = g' * x) →
          Jacquet.IsIwahoriContraction K Nf Mf Nbarf g' →
          ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
            (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
            Jacquet.powerKernelSup ρ hρ K hK g' = Jacquet.powerKernelSup ρ hρ K hK g ∧
              Jacquet.stableImage ρ hρ K hK g' = Jacquet.stableImage ρ hρ K hK g) ∧
        -- Remark 2
        ∃ (C : OpenSubgroup Nf) (hC : IsCompact (C : Set Nf))
          (Cbar : OpenSubgroup Nbarf) (hCbar : IsCompact (Cbar : Set Nbarf)),
          ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
            (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
            let eC : V →ₗ[ℂ] V := Compact.averageMap (ρ.comp Nf.subtype)
              (isSmooth_comp Nf.subtype continuous_subtype_val hρ) C hC
            let eCbar : V →ₗ[ℂ] V := Compact.averageMap (ρ.comp Nbarf.subtype)
              (isSmooth_comp Nbarf.subtype continuous_subtype_val hρ) Cbar hCbar
            Jacquet.powerKernelSup ρ hρ K hK g =
                LinearMap.ker (eC.comp (fixedVectors ρ K.toSubgroup).subtype) ∧
              (Jacquet.stableImage ρ hρ K hK g).map (fixedVectors ρ K.toSubgroup).subtype =
                LinearMap.range ((Compact.averageMap ρ hρ K hK).comp eCbar)

end Langlands.Aubert.General.RepresentedParabolic
