import Langlands.Global.AdelicGroupDiscreteSpectrumReduction
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicIntertwiningNormalizedLevi
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # The finite discrete content of square-integrable automorphic forms: reduction to two inputs

`SquareIntegrableFormFiniteProjectionStatement` (module
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`) says that, for a presented parabolic
`p : P → G` that is an isomorphism, the orthogonal projections of the class of a finite linear
combination of elements of Lapid's `A²_P` onto the closed `G(𝔸)`-invariant subspaces of
`L²([G])` lie in one finite-dimensional subspace. It follows from two propositions:

* `ParabolicHarishChandraFinitenessStatement` (module
  `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`; Harish-Chandra's
  finiteness theorem, Borel–Jacquet 1979, §4.3 (i)), used for the parabolic `P = G`;
* `SquareIntegrableProjectionAutomorphyStatement`: the orthogonal projection onto a closed
  invariant subspace of the class of a smooth square-integrable function of a fixed type
  `(J, L, E)` on `[G]` is the class of an automorphic form of the same type (Harish-Chandra's
  reproducing function, Getz–Hahn 2024, Theorem 6.2.4 and the proof of Corollary 6.2.5; the
  idempotent of a compact open subgroup, Borel–Jacquet 1979, §3.2 and §4.2; the folding estimate
  of Mœglin–Waldspurger 1995, I.2.4–I.2.5).

The theorem `squareIntegrableFormFiniteProjection_of_reduction` derives the first statement from
the two. Along the way the module proves, for a presented `p` that is an isomorphism, that
`U(𝔸) M(F) = G(F)` and that Lapid's `A^n_P` condition gives left invariance under `A_G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints

section Statement

/-- The projections of a square-integrable function of fixed type are automorphic forms of the
same type (derived: Harish-Chandra's reproducing function, Getz–Hahn 2024, Theorem 6.2.4, p.160,
with the proof of Corollary 6.2.5; the idempotent `e_L` of a compact open subgroup, Borel–Jacquet
1979, §3.2, p.194, and §4.2, p.195; the folding estimate of Mœglin–Waldspurger 1995, I.2.4,
pp.25–26, and I.2.5, Lemma (b), p.27). Let `G` be a connected reductive group over a number field
`F`, `K` a maximal compact subgroup of `G(𝔸)` with archimedean part
`K_∞ = K.comap (ofInfinite F G)`, `rho` a closed matrix embedding, `J` an ideal of finite
codimension of the centre `𝔷` of the enveloping algebra, `L` an open subgroup of `G(𝔸_f)` and
`E` a finite-dimensional space of functions on `K_∞`. Let `φ : G(𝔸) → ℂ` be left invariant under
`G(F)` and under `A_G`, smooth (`IsAdelicSmoothFunction`), right invariant under `L`, with every
infinite slice annihilated by `J` and every function `k ↦ φ(g k)` in `E`, and let
`f ∈ L²([G])` be the class of `y ↦ φ(y.out)`. Then for every closed subspace `V` of `L²([G])`
invariant under the right regular representation, the orthogonal projection of `f` onto `V` is
the class of `y ↦ ψ(y.out)` for a function `ψ` that is an automorphic form on `G(F) \ G(𝔸)`
(`IsAutomorphicFunctionOn` for `G(F)`, `K_∞` and `rho`, so in particular of moderate growth),
is left invariant under `A_G` and has the same type `(J, L, E)`. -/
def SquareIntegrableProjectionAutomorphyStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (J : Ideal (AdelicEnvelopingCenter F G hsmooth)),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) →
    ∀ (L : Subgroup (FiniteAdelicGroupPoints F G)),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) →
    ∀ (E : Submodule ℂ (K.comap (ofInfinite F G).toMonoidHom → ℂ)), FiniteDimensional ℂ E →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
      IsLeftInvariantUnder F G (rationalSubgroup F G) φ →
      IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ →
      IsAdelicSmoothFunction F G φ →
      (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, φ (g * ofFinite F G b) = φ g) →
      (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
        ∀ h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G,
          plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G φ b, h⟩ = 0) →
      (∀ g : AdelicGroupPoints F G,
        (fun k : K.comap (ofInfinite F G).toMonoidHom => φ (g * ofInfinite F G k)) ∈ E) →
    ∀ (f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)),
      f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] (fun y => φ y.out) →
    ∀ (V : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)))
      [V.HasOrthogonalProjection],
      (∀ (g : AdelicGroupPoints F G), ∀ x ∈ V,
        RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG
          g x ∈ V) →
      ∃ ψ : AdelicGroupPoints F G → ℂ,
        IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
            (K.comap (ofInfinite F G).toMonoidHom) rho ψ ∧
          IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) ψ ∧
          (∀ b ∈ L, ∀ g : AdelicGroupPoints F G, ψ (g * ofFinite F G b) = ψ g) ∧
          (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
            ∀ h : functionInfiniteSlice F G ψ b ∈ InfinitePlotSmoothFunctions F G,
              plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G ψ b, h⟩ = 0) ∧
          (∀ g : AdelicGroupPoints F G,
            (fun k : K.comap (ofInfinite F G).toMonoidHom => ψ (g * ofInfinite F G k)) ∈ E) ∧
          V.starProjection f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] (fun y => ψ y.out)

end Statement

section IsoParabolic

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- For a presented parabolic `p` that is an isomorphism, `U(𝔸) M(F) = G(F)` in `G(𝔸)`: the
unipotent radical of the connected reductive group `P ≅ G` is trivial, and `l ≫ p` is an
isomorphism, so `M(F)` maps onto `G(F)`. -/
theorem parabolicQuotientSubgroup_eq_rationalSubgroup_of_isIso (hG : IsConnectedReductive G)
    (r : ParabolicRootPresentation p l a) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    [IsIso p] : parabolicQuotientSubgroup F p iU l = rationalSubgroup F G := by
  have : IsIso l := r.isCompatible.levi.isIso_of_isIso_parabolic (p := p) hG
  have hPred : IsConnectedReductive P := hG.of_iso (asIso p)
  have hU1 := hU.1
  have hrad : SubgroupFunctor.range iU = ⊥ :=
    hPred.hasTrivialUnipotentRadical U iU hU1.isClosedSubgroup hU1.smooth
      hU1.connectedSpace hU1.isUnipotent hU1.isNormal
  have hUnip : parabolicUnipotentImage F p iU = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot]
    have hx : x ≫ iU.hom.hom ∈ (SubgroupFunctor.range iU).carrier _ :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    rw [hrad] at hx
    change x ≫ iU.hom.hom = 1 at hx
    change x ≫ (iU ≫ p).hom.hom = 1
    rw [Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
  have hRat : parabolicLeviRationalImage F p l = rationalSubgroup F G := by
    change rationalImage F (l ≫ p) = rationalSubgroup F G
    apply le_antisymm (rationalImage_le_rationalSubgroup _) ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨G.affinePointsTarget (inv (l ≫ p)) (CommAlgCat.of F F) x, ?_⟩
    change map F M G (l ≫ p) (rational F M
      (G.affinePointsTarget (inv (l ≫ p)) (CommAlgCat.of F F) x)) = rational F G x
    rw [map_rational_affinePointsTarget, IsIso.inv_hom_id]
    change rational F G x ≫ 𝟙 G.X = rational F G x
    exact Category.comp_id _
  change parabolicUnipotentImage F p iU ⊔ parabolicLeviRationalImage F p l = _
  rw [hUnip, hRat, bot_sup_eq]

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

/-- For a presented parabolic `p` that is an isomorphism, a function satisfying Lapid's `A^n_P`
condition `IsSplitComponentEquivariant p l` is left invariant under `A_G`: the isomorphism
`l ≫ p` carries `A_M` onto `A_G`, and `m ↦ m^{ρ_P}` is trivial on `l(A_M)` because the canonical
split component of `M` maps centrally into `G`. -/
theorem isLeftInvariantUnder_canonicalSubgroup_of_isIso (hG : IsConnectedReductive G)
    (r : ParabolicRootPresentation p l a) [IsIso p] {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ) :
    IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) φ := by
  have : IsIso l := r.isCompatible.levi.isIso_of_isIso_parabolic (p := p) hG
  intro x hx g
  let e : M ≅ G := asIso (l ≫ p)
  have hymem : map F G M e.inv x ∈ RestrictionSplitCentre.canonicalSubgroup F M :=
    RestrictionSplitCentre.map_mem_canonicalSubgroup e.symm hx
  have hyx : map F P G p (map F M P l (map F G M e.inv x)) = x := by
    simp only [e, map_apply, GroupScheme.affinePointsTarget_apply, Category.assoc,
      ← Grp.comp_hom_hom, asIso_inv, IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hpow :
      parameterPower F P (halfModulusParameter F P) (map F M P l (map F G M e.inv x)) = 1 := by
    have hy := hymem
    rw [RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup] at hy
    obtain ⟨t, -, ht⟩ := hy
    have hT := RestrictionSplitCentre.isSplitComponent_canonicalComponent F M
    have hc : IsCentral ((RestrictionSplitCentre.canonicalComponent F M ≫ l) ≫ p) := by
      rw [Category.assoc]
      exact hT.isCentralSplitTorus.isCentral.comp_iso (asIso (l ≫ p))
    have : IsAffineHom (RestrictionSplitCentre.canonicalTorus F M).toGrp.X.hom :=
      hT.1.1.1.isAffineHom
    have : IsAffine (RestrictionSplitCentre.canonicalTorus F M).toGrp.X.left :=
      isAffine_of_isAffineHom (RestrictionSplitCentre.canonicalTorus F M).toGrp.X.hom
    have : Mono p.hom.hom := Over.mono_of_mono_left _
    have h1 := parameterPower_halfModulus_map_of_isCentral hc t
    rw [map_comp_apply_of_hom (p := l)] at h1
    rw [← ht]
    exact h1
  have h := hφ _ hymem g
  rw [hyx, hpow, one_mul] at h
  exact h

end IsoParabolic

section Closure

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- The infinite slice of a finite linear combination is the combination of the slices. -/
theorem functionInfiniteSlice_sum {k : ℕ} (c : Fin k → ℂ) (v : Fin k → AdelicGroupPoints F G → ℂ)
    (b : FiniteAdelicGroupPoints F G) :
    functionInfiniteSlice F G (fun y => ∑ j, c j * v j y) b =
      ∑ j, c j • functionInfiniteSlice F G (v j) b := by
  funext x
  simp [functionInfiniteSlice, Finset.sum_apply]

/-- Finite linear combinations of smooth functions on `G(𝔸)` are smooth: the level is the
intersection of the levels. -/
theorem isAdelicSmoothFunction_sum {k : ℕ} (c : Fin k → ℂ)
    (v : Fin k → AdelicGroupPoints F G → ℂ) (hv : ∀ j, IsAdelicSmoothFunction F G (v j)) :
    IsAdelicSmoothFunction F G (fun y => ∑ j, c j * v j y) := by
  choose L hLo hL using fun j => (hv j).2.2
  refine ⟨continuous_finsetSum _ fun j _ => continuous_const.mul (hv j).1, fun b => ?_,
    ⨅ j, L j, ?_, ?_⟩
  · rw [functionInfiniteSlice_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((hv j).2.1 b)
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hLo
  · intro x hx g
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hL j x (Subgroup.mem_iInf.mp hx j) g]

/-- Finite linear combinations of `K_∞`-finite functions are `K_∞`-finite. -/
theorem isInfiniteSubgroupFiniteFunction_sum {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {k : ℕ} (c : Fin k → ℂ) (v : Fin k → AdelicGroupPoints F G → ℂ)
    (hv : ∀ j, IsInfiniteSubgroupFiniteFunction F G Kinf (v j)) :
    IsInfiniteSubgroupFiniteFunction F G Kinf (fun y => ∑ j, c j * v j y) := by
  let S : Fin k → Submodule ℂ (AdelicGroupPoints F G → ℂ) := fun j =>
    Submodule.span ℂ (Set.range fun κ : Kinf =>
      fun g : AdelicGroupPoints F G => v j (g * AdelicGroupPoints.ofInfinite F G κ))
  have : ∀ j, FiniteDimensional ℂ (S j) := hv
  have hle : Submodule.span ℂ (Set.range fun κ : Kinf =>
      fun g : AdelicGroupPoints F G =>
        (fun y => ∑ j, c j * v j y) (g * AdelicGroupPoints.ofInfinite F G κ)) ≤ ⨆ j, S j := by
    rw [Submodule.span_le]
    rintro _ ⟨κ, rfl⟩
    have heq : (fun g : AdelicGroupPoints F G =>
        ∑ j, c j * v j (g * AdelicGroupPoints.ofInfinite F G κ)) =
        ∑ j, c j • fun g : AdelicGroupPoints F G => v j (g * AdelicGroupPoints.ofInfinite F G κ) := by
      funext g
      simp [Finset.sum_apply]
    show (fun g : AdelicGroupPoints F G =>
        ∑ j, c j * v j (g * AdelicGroupPoints.ofInfinite F G κ)) ∈ ⨆ j, S j
    rw [heq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j (Submodule.subset_span ⟨κ, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

/-- For a `K_∞`-finite function `φ`, the functions `k ↦ φ(g k)` on `K_∞` span a
finite-dimensional space: each is the image of evaluation at `g` under the linear map
`ℓ ↦ (k ↦ ℓ(φ(· k)))` on the dual of the finite-dimensional span of the right translates. -/
theorem finiteDimensional_span_infiniteSlices {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {φ : AdelicGroupPoints F G → ℂ} (hφ : IsInfiniteSubgroupFiniteFunction F G Kinf φ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g : AdelicGroupPoints F G =>
      fun κ : Kinf => φ (g * AdelicGroupPoints.ofInfinite F G κ))) := by
  let S := Submodule.span ℂ (Set.range fun κ : Kinf =>
    fun g : AdelicGroupPoints F G => φ (g * AdelicGroupPoints.ofInfinite F G κ))
  have : FiniteDimensional ℂ S := hφ
  let Ψ : Module.Dual ℂ S →ₗ[ℂ] (Kinf → ℂ) :=
    { toFun := fun ℓ κ => ℓ ⟨fun g => φ (g * AdelicGroupPoints.ofInfinite F G κ),
        Submodule.subset_span ⟨κ, rfl⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : Submodule.span ℂ (Set.range fun g : AdelicGroupPoints F G =>
      fun κ : Kinf => φ (g * AdelicGroupPoints.ofInfinite F G κ)) ≤ LinearMap.range Ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨(LinearMap.proj g : (AdelicGroupPoints F G → ℂ) →ₗ[ℂ] ℂ).comp S.subtype, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

/-- A finite intersection of ideals of finite codimension has finite codimension. -/
theorem finite_quotient_iInf {Z : Type*} [CommRing Z] [Algebra ℂ Z] {k : ℕ}
    (J : Fin k → Ideal Z) (hJ : ∀ j, Module.Finite ℂ (Z ⧸ (J j).restrictScalars ℂ)) :
    Module.Finite ℂ (Z ⧸ (⨅ j, J j).restrictScalars ℂ) := by
  let f : Z →ₗ[ℂ] ((j : Fin k) → Z ⧸ (J j).restrictScalars ℂ) :=
    LinearMap.pi fun j => ((J j).restrictScalars ℂ).mkQ
  have hker : LinearMap.ker f = (⨅ j, J j).restrictScalars ℂ := by
    ext z
    simp [f, LinearMap.mem_ker, funext_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_iInf]
  rw [← hker]
  exact Module.Finite.of_injective ((LinearMap.ker f).liftQ f le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))

/-- A finite linear combination `φ = ∑ j, c j · v j` of automorphic functions has a type: an ideal
`J` of finite codimension of `𝔷` (the intersection of annihilating ideals), an open subgroup `L`
of `G(𝔸_f)` (the intersection of levels) and a finite-dimensional space `E` of functions on
`K_∞` (the span of the functions `k ↦ φ(g k)`), with `φ` right invariant under `L`, its slices
annihilated by `J` and every `k ↦ φ(g k)` in `E`. -/
theorem exists_combination_type {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (rho : MatrixRepresentation G (Fin N))
    (Γ : Subgroup (AdelicGroupPoints F G)) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {k : ℕ} (c : Fin k → ℂ) (v : Fin k → AdelicGroupPoints F G → ℂ)
    (hv : ∀ j, IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho (v j)) :
    ∃ J : Ideal (AdelicEnvelopingCenter F G hsmooth),
      Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
    ∃ E : Submodule ℂ (Kinf → ℂ), FiniteDimensional ℂ E ∧
      (∀ b ∈ L, ∀ g : AdelicGroupPoints F G,
        (fun y => ∑ j, c j * v j y) (g * ofFinite F G b) = (fun y => ∑ j, c j * v j y) g) ∧
      (∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
        ∀ h : functionInfiniteSlice F G (fun y => ∑ j, c j * v j y) b ∈
            InfinitePlotSmoothFunctions F G,
          plotSmoothCenterAction F G hsmooth hcalc z
            ⟨functionInfiniteSlice F G (fun y => ∑ j, c j * v j y) b, h⟩ = 0) ∧
      (∀ g : AdelicGroupPoints F G,
        (fun κ : Kinf => (fun y => ∑ j, c j * v j y) (g * ofInfinite F G κ)) ∈ E) := by
  choose L₀ hL₀o hL₀ using fun j => (hv j).2.1.2.2
  choose J₀ hJ₀f hJ₀ using fun j => (hv j).2.2.2.1
  refine ⟨⨅ j, J₀ j, ?_, ⨅ j, L₀ j, ?_,
    Submodule.span ℂ (Set.range fun g : AdelicGroupPoints F G =>
      fun κ : Kinf => (fun y => ∑ j, c j * v j y) (g * ofInfinite F G κ)), ?_, ?_, ?_, ?_⟩
  · exact finite_quotient_iInf J₀ hJ₀f
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hL₀o
  · exact finiteDimensional_span_infiniteSlices (Kinf := Kinf) (φ := fun y => ∑ j, c j * v j y)
      (isInfiniteSubgroupFiniteFunction_sum c v fun j => (hv j).2.2.1)
  · intro b hb g
    exact Finset.sum_congr rfl fun j _ => by rw [hL₀ j b (Subgroup.mem_iInf.mp hb j) g]
  · intro z hz b h
    have hsl : ∀ j, functionInfiniteSlice F G (v j) b ∈ InfinitePlotSmoothFunctions F G :=
      fun j => (hv j).2.1.2.1 b
    have heq : (⟨functionInfiniteSlice F G (fun y => ∑ j, c j * v j y) b, h⟩ :
        InfinitePlotSmoothFunctions F G) =
        ∑ j, c j • (⟨functionInfiniteSlice F G (v j) b, hsl j⟩ :
          InfinitePlotSmoothFunctions F G) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact functionInfiniteSlice_sum c v b
    rw [heq, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, hJ₀ j z ((Submodule.mem_iInf _).mp hz j) b (hsl j), smul_zero]
  · exact fun g => Submodule.subset_span ⟨g, rfl⟩

end Closure

section L2

/-- The `L²` classes that are almost everywhere equal to `y ↦ ψ(o y)` for some `ψ` in a
finite-dimensional space `S` of functions lie in one finite-dimensional subspace of `L²`: the
image of the square-integrable part of `S` under the class map. -/
theorem exists_finiteDimensional_of_ae_eq {X Y : Type*} [MeasurableSpace X] (m : Measure X)
    (o : X → Y) {S : Submodule ℂ (Y → ℂ)} (hS : FiniteDimensional ℂ S) :
    ∃ W : Submodule ℂ (Lp ℂ 2 m), FiniteDimensional ℂ W ∧
      ∀ x : Lp ℂ 2 m, ∀ ψ ∈ S, x =ᵐ[m] (fun y => ψ (o y)) → x ∈ W := by
  have := hS
  let T : Submodule ℂ (Y → ℂ) :=
    { carrier := {ψ | ψ ∈ S ∧ MemLp (fun y => ψ (o y)) 2 m}
      add_mem' := fun ha hb => ⟨S.add_mem ha.1 hb.1, ha.2.add hb.2⟩
      zero_mem' := ⟨S.zero_mem, MemLp.zero⟩
      smul_mem' := fun c' _ hψ => ⟨S.smul_mem c' hψ.1, hψ.2.const_smul c'⟩ }
  have : FiniteDimensional ℂ T :=
    Submodule.finiteDimensional_of_le (S₁ := T) (S₂ := S) fun ψ hψ =>
      (show ψ ∈ S ∧ MemLp (fun y => ψ (o y)) 2 m from hψ).1
  let Φ : T →ₗ[ℂ] Lp ℂ 2 m :=
    { toFun := fun ψ => ψ.2.2.toLp _
      map_add' := fun ψ₁ ψ₂ => MemLp.toLp_add ψ₁.2.2 ψ₂.2.2
      map_smul' := fun c' ψ => MemLp.toLp_const_smul c' ψ.2.2 }
  refine ⟨LinearMap.range Φ, inferInstance, fun x ψ hψ hx => ?_⟩
  have hψm : MemLp (fun y => ψ (o y)) 2 m := (Lp.memLp x).ae_eq hx
  exact ⟨⟨ψ, hψ, hψm⟩, Lp.ext (hψm.coeFn_toLp.trans hx.symm)⟩

end L2

/-- Harish-Chandra's finiteness theorem and the automorphy of the projections give the finite
discrete content of square-integrable automorphic forms. -/
theorem squareIntegrableFormFiniteProjection_of_reduction
    (hHC : ParabolicHarishChandraFinitenessStatement.{0})
    (hB : SquareIntegrableProjectionAutomorphyStatement) :
    SquareIntegrableFormFiniteProjectionStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P M U A _ _ _ _ p _ iU l a r hU hK hp
    f k v c hv hf
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : IsIso p := hp
  have : Smooth G.X.hom := hG.smooth
  have hΓ := parabolicQuotientSubgroup_eq_rationalSubgroup_of_isIso hG r hU
  have hv1 : ∀ j, IsAutomorphicFunctionOn F G hsmooth hcalc (rationalSubgroup F G)
      (K.comap (ofInfinite F G).toMonoidHom) rho (v j) := fun j => by
    rw [← hΓ]
    exact (hv j).1
  obtain ⟨J, hJfin, L, hLo, E, hEfin, hφL, hφJ, hφE⟩ :=
    exists_combination_type hsmooth hcalc rho _ _ c v hv1
  have hφleft : IsLeftInvariantUnder F G (rationalSubgroup F G) (fun y => ∑ j, c j * v j y) :=
    fun x hx g => Finset.sum_congr rfl fun j _ => by rw [(hv1 j).1 x hx g]
  have hφcent : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G)
      (fun y => ∑ j, c j * v j y) :=
    fun x hx g => Finset.sum_congr rfl fun j _ => by
      rw [isLeftInvariantUnder_canonicalSubgroup_of_isIso hG r (hv j).2.1 x hx g]
  have hφsm : IsAdelicSmoothFunction F G (fun y => ∑ j, c j * v j y) :=
    isAdelicSmoothFunction_sum c v fun j => (hv1 j).2.1
  have hmul : IsIso (subgroupMultiplication l iU) := r.isIso_subgroupMultiplication_of_radical hU
  have hfin := hHC F G P M U p iU l hG r.isCompatible.parabolic hU r.isCompatible.levi hmul K
    hKmax hK rho hsmooth hcalc hrho J hJfin L hLo E hEfin
  obtain ⟨W, hW, hWmem⟩ := exists_finiteDimensional_of_ae_eq
    (RestrictionSplitCentre.canonicalMeasure F G) (fun y => y.out) hfin
  refine ⟨W, hW, fun V _ hV => ?_⟩
  obtain ⟨ψ, hψaut, -, hψL, hψJ, hψE, hψf⟩ := hB F G hG K rho hsmooth hcalc hKmax hrho J hJfin
    L hLo E hEfin _ hφleft hφcent hφsm hφL hφJ hφE f hf V hV
  exact hWmem _ ψ (Submodule.subset_span ⟨by rwa [hΓ], hψL, hψJ, hψE⟩) hψf

end Langlands.Global
