import Langlands.BushnellKutzko.SplitTypeExistenceSteps
import Langlands.BushnellKutzko.LevelZeroRefinement
import Langlands.BushnellKutzko.PrincipalChainResidueDegree
import Langlands.Representation.FiniteGeneralLinear.FiniteProductConstituent
import Langlands.Representation.Filtration.LengthTwoMatching

/-! # Level-zero type containment (BK93 (8.1.5), first case)

An irreducible smooth representation `π` of `GL_N(F)` with a nonzero vector fixed by `U^1(𝔄)`,
for the hereditary order `𝔄` of some lattice chain, contains a simple type of level zero or a
split type of level `(0, 0)`.

The proof follows BK93, printed pp. 267–268 (PDF pp. 279–280), with the minimal hereditary
order there replaced by strong induction on `N - e(𝓛)` (the period `e(𝓛)` is at most `N`). Let
`𝓛` be a lattice chain for which `π` has a nonzero `U^1(𝓛)`-fixed vector. The `U^1(𝓛)`-fixed
vectors form a representation of `U(𝓛) / U^1(𝓛) ≅ ∏_i GL(L_i / L_{i+1})`, which contains an
irreducible constituent `⊗_i ρ_i`. If some `ρ_i` is not cuspidal, inserting one lattice into the
chain gives a nonzero vector fixed by `U^1` of a chain of larger period
(`LatticeChain.exists_refinement_of_not_isCuspidal`), and the induction hypothesis applies to
that chain. Otherwise all `ρ_i` are cuspidal, and `π`
contains the inflation of `⊗_i ρ_i` to `U(𝓛)`: it is a split type of level `(0, 0)` if two of
the factors are inequivalent, and a simple type of level zero (with a principal order) if all of
them are equivalent.
-/

open IsLocalRing Module ValuativeRel Langlands.FiniteRep

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uπ uρ uV uW

section Constituent

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- **An irreducible constituent of the `U^1(𝔄)`-fixed vectors.** Let `τ` be a representation of
`Aut_F(V)` on `W` and let `w ≠ 0` be fixed by `U^1(𝔄)`. Let `d_i` be the dimension of
`L_i / L_{i+1}`, `0 ≤ i < e`, with basis `b_i`. There are irreducible classes `a_i` of
`GL_{d_i}(k_F)`, with representatives `ρ_i`, and an injective linear map from `⊗_i ρ_i` to `W`
carrying the inflation of `⊗_i ρ_i` along the layer reduction `U(𝔄) → ∏_i GL_{d_i}(k_F)` to the
restriction of `τ` to `U(𝔄)`. -/
theorem LatticeChain.exists_layer_constituent (L : LatticeChain 𝒪[F] F V)
    {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField 𝒪[F]) (L.Layer (i : ℕ)))
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Module.End F V)ˣ W)
    {w : W} (hw : w ≠ 0) (hfix : ∀ g ∈ L.unitFiltration 1, τ g w = w) :
    ∃ (a : ∀ i, IrreducibleClass (GeneralLinear (d i) (ResidueField 𝒪[F])))
      (f : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type)) →ₗ[ℂ] W),
      Function.Injective f ∧ ∀ (g : L.unitFiltration 0)
        (x : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type))),
        f (FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ)
          (L.layerReduction b g) x) = τ g (f x) := by
  classical
  let φ := L.layerReduction b
  have hs : Function.Surjective φ := L.layerReduction_surjective b
  let τ₀ : Representation ℂ (L.unitFiltration 0) W := τ.comp (L.unitFiltration 0).subtype
  let X := Representation.invariants (τ₀.comp φ.ker.subtype)
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hs
  let σ : Representation ℂ (∀ i, GeneralLinear (d i) (ResidueField 𝒪[F])) X :=
    (Representation.quotientToInvariants τ₀ φ.ker).comp e.symm.toMonoidHom
  have hw₀ : w ∈ X := by
    rw [Representation.mem_invariants]
    intro g
    exact hfix _ (L.mem_unitFiltration_one_of_layerReduction_eq_one b g.1 g.2)
  have hne : (⟨w, hw₀⟩ : X) ≠ 0 := fun h => hw (congrArg Subtype.val h)
  obtain ⟨a, f, hf, hfσ⟩ := exists_externalRep_intertwining σ hne
  refine ⟨a, X.subtype ∘ₗ f, Subtype.val_injective.comp hf, fun g x => ?_⟩
  have he : e.symm (φ g) = (g : L.unitFiltration 0 ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h1 := congrArg Subtype.val (hfσ (φ g) x)
  change ((f ((externalRep fun i => VirtualCharacter.rep (a i)).ρ (φ g) x) : X) : W) =
    τ g (f x : W)
  refine h1.trans ?_
  change ((Representation.quotientToInvariants τ₀ φ.ker (e.symm (φ g)) (f x) : X) : W) = _
  rw [he]
  rfl

end Constituent

section Transport

variable {G : Type*} [Group G]

/-- A finite-dimensional representation, transported to coordinates in a chosen basis. -/
private def coordinateRep (V : FDRep ℂ G) : Representation ℂ G (Fin (finrank ℂ V) → ℂ) :=
  (MonoidHom.ofClass ((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ)).comp V.ρ

/-- The coordinate isomorphism as an equivalence of representations. -/
private def coordinateEquiv (V : FDRep ℂ G) : Representation.Equiv V.ρ (coordinateRep V) :=
  Representation.Equiv.mk (Module.finBasis ℂ V).equivFun fun g => by
    apply LinearMap.ext
    intro x
    change _ = (Module.finBasis ℂ V).equivFun
      (V.ρ g ((Module.finBasis ℂ V).equivFun.symm ((Module.finBasis ℂ V).equivFun x)))
    rw [LinearEquiv.symm_apply_apply]
    rfl

/-- An irreducible representation over a field has a nontrivial carrier. -/
private theorem nontrivial_of_isIrreducible' {k : Type*} {X : Type*} [Field k]
    [AddCommGroup X] [Module k X] {ρ : Representation k G X}
    (h : Representation.IsIrreducible ρ) : Nontrivial X := by
  have : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  exact IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule

end Transport

section Matrix

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

/-- The cuspidal layer data given by bases of the layers and irreducible cuspidal classes of
the layer groups, with the factors realized in coordinates. -/
private def cuspidalData {V : Type uV} [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) {d : Fin L.period → ℕ}
    (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField 𝒪[F]) (L.Layer (i : ℕ)))
    (a : ∀ i, IrreducibleClass (GeneralLinear (d i) (ResidueField 𝒪[F])))
    (hcusp : ∀ i, FiniteGeneralLinear.IsCuspidal (VirtualCharacter.rep (a i)).ρ) :
    L.CuspidalLayerData where
  rank := d
  dim i := finrank ℂ (VirtualCharacter.rep (a i))
  basis := b
  factor i := coordinateRep (VirtualCharacter.rep (a i))
  cuspidal i := ⟨LengthTwo.isIrreducible_of_equiv (coordinateEquiv _)
      (VirtualCharacter.isIrreducible_rep _), (hcusp i).of_equiv (coordinateEquiv _)⟩

/-- A lattice chain whose layers in one period all have dimension `r` is principal. -/
private theorem isPrincipal_of_bases {V : Type uV} [AddCommGroup V] [Module F V]
    (L : LatticeChain 𝒪[F] F V) {r : ℕ}
    (b : ∀ i : Fin L.period, Module.Basis (Fin r) (ResidueField 𝒪[F]) (L.Layer (i : ℕ))) :
    L.IsPrincipal := by
  have key : ∀ j : ℤ, (L.lattice (j + 1)).toAddSubgroup.relIndex (L.lattice j).toAddSubgroup =
      Nat.card (ResidueField 𝒪[F]) ^ r := by
    intro j
    obtain ⟨s, ⟨e⟩⟩ := L.exists_layer_linearEquiv j
    rw [← L.natCard_interval_eq_relIndex j (j + 1)]
    change Nat.card (L.Layer j) = _
    rw [← Nat.card_congr e.toEquiv]
    have : Module.Finite (ResidueField 𝒪[F]) (L.Layer (s : ℕ)) := Module.Finite.of_basis (b s)
    rw [Module.natCard_eq_pow_finrank (K := ResidueField 𝒪[F]),
      Module.finrank_eq_card_basis (b s), Fintype.card_fin]
  intro i j
  rw [key, key]

/-- The unit group `U(𝔄)` of the order of `L`, as a subgroup of `GL_n(F)`. -/
private def matrixUnitGroup (L : LatticeChain 𝒪[F] F (Fin n → F)) :
    Subgroup (GeneralLinear n F) :=
  (L.unitFiltration 0).comap (toAut).toMonoidHom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem glSubgroupToAut_matrixUnitGroup (L : LatticeChain 𝒪[F] F (Fin n → F)) :
    glSubgroupToAut (matrixUnitGroup L) = L.unitFiltration 0 :=
  Subgroup.map_comap_eq_self_of_surjective (toAut).surjective _

/-- The identification of the matrix unit group with `U(𝔄)`. -/
private def matrixUnitGroupHom (L : LatticeChain 𝒪[F] F (Fin n → F)) :
    matrixUnitGroup L →* L.unitFiltration 0 :=
  ((toAut).toMonoidHom.comp (matrixUnitGroup L).subtype).codRestrict _ fun x => x.2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem matrixUnitGroupHom_symm (L : LatticeChain 𝒪[F] F (Fin n → F))
    (x : glSubgroupToAut (matrixUnitGroup L)) :
    ((matrixUnitGroupHom L ((glSubgroupToAutEquiv (matrixUnitGroup L)).symm x) :
      L.unitFiltration 0) : Aut) = x :=
  congrArg Subtype.val ((glSubgroupToAutEquiv (matrixUnitGroup L)).apply_symm_apply x)

/-- The inflation of the cuspidal layer data to the matrix unit group, on a carrier lifted to
the universe `uρ`. -/
private def liftedInflation {L : LatticeChain 𝒪[F] F (Fin n → F)} (A : L.CuspidalLayerData) :
    Representation ℂ (matrixUnitGroup L)
      (ULift.{uρ} (PiTensorProduct ℂ fun i => Fin (A.dim i) → ℂ)) :=
  (MonoidHom.ofClass
      ((ULift.moduleEquiv : ULift.{uρ} (PiTensorProduct ℂ fun i => Fin (A.dim i) → ℂ) ≃ₗ[ℂ]
        _).symm.conjAlgEquiv ℂ)).comp
    (A.inflation.comp (matrixUnitGroupHom L))

private theorem inflation_eq_one {L : LatticeChain 𝒪[F] F (Fin n → F)} (A : L.CuspidalLayerData)
    (g : L.unitFiltration 0) (hg : (g : Aut) ∈ L.unitFiltration 1) : A.inflation g = 1 := by
  have h1 : L.layerReduction A.basis g = 1 := L.layerReduction_eq_one_of_mem _ _ hg
  simp only [LatticeChain.CuspidalLayerData.inflation, MonoidHom.comp_apply, h1, map_one]

private local instance levelZeroEndTopology : TopologicalSpace (Module.End F (Fin n → F)) :=
  moduleTopology F _

private theorem isSmooth_liftedInflation {L : LatticeChain 𝒪[F] F (Fin n → F)}
    (A : L.CuspidalLayerData) : IsSmooth (liftedInflation.{uF, uρ} A) := by
  intro v
  let H : Subgroup (matrixUnitGroup L) :=
    (L.unitFiltration 1).comap ((toAut).toMonoidHom.comp (matrixUnitGroup L).subtype)
  have hH : IsOpen (H : Set (matrixUnitGroup L)) :=
    (isOpen_unitFiltration L 1).preimage
      ((generalLinearToLinContinuous (F := F) (n := n)).continuous.comp continuous_subtype_val)
  refine ⟨⟨H, hH⟩, ?_⟩
  rw [fixedVectors, Representation.mem_invariants]
  intro g
  have h1 := inflation_eq_one A (matrixUnitGroupHom L g) g.2
  change ULift.up (A.inflation (matrixUnitGroupHom L g) v.down) = v
  rw [h1]
  rfl

/-- The inflation of the cuspidal layer data, as a smooth representation of the matrix unit
group. -/
private def inflationSmoothRep {L : LatticeChain 𝒪[F] F (Fin n → F)} (A : L.CuspidalLayerData) :
    SmoothRep.{0, uF, uρ} ℂ (matrixUnitGroup L) :=
  SmoothRep.of (liftedInflation.{uF, uρ} A) (isSmooth_liftedInflation A)

private theorem isPairIsomorphic_inflationSmoothRep {L : LatticeChain 𝒪[F] F (Fin n → F)}
    (A : L.CuspidalLayerData) :
    IsPairIsomorphic (glRepresentationToAut (inflationSmoothRep.{uF, uρ} A)) A.inflation := by
  refine ⟨glSubgroupToAut_matrixUnitGroup L, ⟨Representation.Equiv.mk ULift.moduleEquiv
    fun u => ?_⟩⟩
  apply LinearMap.ext
  intro x
  have hu : matrixUnitGroupHom L ((glSubgroupToAutEquiv (matrixUnitGroup L)).symm
      ((MulEquiv.subgroupCongr (glSubgroupToAut_matrixUnitGroup L)).symm u)) = u :=
    Subtype.ext (matrixUnitGroupHom_symm L _)
  change A.inflation (matrixUnitGroupHom L ((glSubgroupToAutEquiv (matrixUnitGroup L)).symm
      ((MulEquiv.subgroupCongr (glSubgroupToAut_matrixUnitGroup L)).symm u))) x.down =
    A.inflation u x.down
  rw [hu]

private theorem inflationSmoothRep_eq_one {L : LatticeChain 𝒪[F] F (Fin n → F)}
    (A : L.CuspidalLayerData) (j : glSubgroupToAut (matrixUnitGroup L))
    (hj : (j : Aut) ∈ L.unitFiltration 1) :
    glRepresentationToAut (inflationSmoothRep.{uF, uρ} A) j = 1 := by
  have h1 := inflation_eq_one A
    (matrixUnitGroupHom L ((glSubgroupToAutEquiv (matrixUnitGroup L)).symm j))
    (by rw [matrixUnitGroupHom_symm]; exact hj)
  apply LinearMap.ext
  intro x
  change ULift.up (A.inflation (matrixUnitGroupHom L
    ((glSubgroupToAutEquiv (matrixUnitGroup L)).symm j)) x.down) = x
  rw [h1]
  rfl

variable {L : LatticeChain 𝒪[F] F (Fin n → F)} {d : Fin L.period → ℕ}
  (b : ∀ i, Module.Basis (Fin (d i)) (ResidueField 𝒪[F]) (L.Layer (i : ℕ)))
  (a : ∀ i, IrreducibleClass (GeneralLinear (d i) (ResidueField 𝒪[F])))
  (hcusp : ∀ i, FiniteGeneralLinear.IsCuspidal (VirtualCharacter.rep (a i)).ρ)

private theorem containsType_inflationSmoothRep (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (f : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type)) →ₗ[ℂ] π)
    (hf : Function.Injective f)
    (hfτ : ∀ (g : L.unitFiltration 0)
      (x : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type))),
      f (FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ)
        (L.layerReduction b g) x) = π.representation ((toAut).symm g) (f x)) :
    ContainsType π (inflationSmoothRep.{uF, uρ} (cuspidalData L b a hcusp)) := by
  classical
  let E (i : Fin L.period) := (Module.finBasis ℂ (VirtualCharacter.rep (a i))).equivFun
  let T : PiTensorProduct ℂ (fun i => Fin ((cuspidalData L b a hcusp).dim i) → ℂ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type)) :=
    PiTensorProduct.congr fun i => (E i).symm
  have hT : ∀ (g : ∀ i, GeneralLinear (d i) (ResidueField 𝒪[F]))
      (y : PiTensorProduct ℂ (fun i => Fin ((cuspidalData L b a hcusp).dim i) → ℂ)),
      T (PiTensorProduct.map (fun i => (cuspidalData L b a hcusp).factor i (g i)) y) =
        FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ) g (T y) := by
    intro g y
    have hlin : T.toLinearMap ∘ₗ
        PiTensorProduct.map (fun i => (cuspidalData L b a hcusp).factor i (g i)) =
        FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ) g ∘ₗ T.toLinearMap := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro m
      change T (PiTensorProduct.map (fun i => (cuspidalData L b a hcusp).factor i (g i))
          (PiTensorProduct.tprod ℂ m)) =
        FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ) g
          (T (PiTensorProduct.tprod ℂ m))
      rw [PiTensorProduct.map_tprod]
      refine (PiTensorProduct.congr_tprod (fun i => (E i).symm) _).trans ?_
      refine Eq.trans ?_ (congrArg _ (PiTensorProduct.congr_tprod (fun i => (E i).symm) m)).symm
      rw [FiniteTensor.external_tprod]
      congr 1
      funext i
      change (E i).symm ((E i) ((VirtualCharacter.rep (a i)).ρ (g i) ((E i).symm (m i)))) = _
      rw [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hlin y
  let Φ : ULift.{uρ} (PiTensorProduct ℂ fun i => Fin ((cuspidalData L b a hcusp).dim i) → ℂ)
      →ₗ[ℂ] π :=
    f ∘ₗ T.toLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap
  refine ⟨⟨Φ, fun k => ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro x
    change f (T (PiTensorProduct.map (fun i => (cuspidalData L b a hcusp).factor i
        (L.layerReduction b (matrixUnitGroupHom L k) i)) x.down)) =
      π.representation (k : GeneralLinear n F) (f (T x.down))
    rw [hT, hfτ]
    change π.representation ((toAut).symm ((toAut) (k : GeneralLinear n F))) _ = _
    rw [MulEquiv.symm_apply_apply]
  · have : ∀ i, Nontrivial (VirtualCharacter.rep (a i)) := fun i =>
      nontrivial_of_isIrreducible' (VirtualCharacter.isIrreducible_rep (a i))
    have hy : ∀ i, ∃ y : VirtualCharacter.rep (a i), y ≠ 0 := fun i => exists_ne 0
    choose y hy using hy
    intro h0
    have h := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0)
      (ULift.up (T.symm (PiTensorProduct.tprod ℂ y)))
    change f (T (T.symm (PiTensorProduct.tprod ℂ y))) = 0 at h
    rw [LinearEquiv.apply_symm_apply, ← map_zero f] at h
    exact tprod_ne_zero_of_forall_ne_zero y hy (hf h)

include hcusp in
/-- **The cuspidal case.** If all the layer constituents are cuspidal, `π` contains the inflation
of their tensor product to `U(𝔄)`: a split type of level `(0, 0)` if two of the factors are
inequivalent, a simple type of level zero otherwise. -/
private theorem exists_type_of_cuspidal (ψF : AddChar F ℂ)
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (f : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type)) →ₗ[ℂ] π)
    (hf : Function.Injective f)
    (hfτ : ∀ (g : L.unitFiltration 0)
      (x : PiTensorProduct ℂ (fun i => (VirtualCharacter.rep (a i) : Type))),
      f (FiniteTensor.external (fun i => (VirtualCharacter.rep (a i)).ρ)
        (L.layerReduction b g) x) = π.representation ((toAut).symm g) (f x)) :
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      (IsGLSimpleType (n := n) ψF ρ ∨
        IsLevelZeroSplitType (V := Fin n → F) (glRepresentationToAut ρ)) := by
  refine ⟨matrixUnitGroup L, inflationSmoothRep.{uF, uρ} (cuspidalData L b a hcusp),
    containsType_inflationSmoothRep b a hcusp π f hf hfτ, ?_⟩
  by_cases h : ∃ i j, (cuspidalData L b a hcusp).factorClass i ≠
      (cuspidalData L b a hcusp).factorClass j
  · exact Or.inr ⟨L, cuspidalData L b a hcusp, h, inflationSmoothRep_eq_one _,
      isPairIsomorphic_inflationSmoothRep _⟩
  · push Not at h
    let i₀ : Fin L.period := ⟨0, L.period_pos⟩
    obtain ⟨r, rfl⟩ : ∃ r, d = fun _ => r :=
      ⟨d i₀, funext fun i => congrArg Sigma.fst (h i i₀)⟩
    have ha : ∀ i, a i = a i₀ := by
      intro i
      have h3 := eq_of_heq (Sigma.ext_iff.mp (h i i₀)).2
      obtain ⟨E⟩ := (FiniteGeneralLinear.CuspidalRep.isoClass_eq_iff _ _).mp h3
      let E' : Representation.Equiv (VirtualCharacter.rep (a i)).ρ
          (VirtualCharacter.rep (a i₀)).ρ :=
        (coordinateEquiv _).trans (E.trans (coordinateEquiv _).symm)
      have hc : classOf (VirtualCharacter.rep (a i)) = classOf (VirtualCharacter.rep (a i₀)) :=
        (classOf_eq_iff _ _).mpr ⟨isoOfEquiv E'⟩
      rw [VirtualCharacter.classOf_rep, VirtualCharacter.classOf_rep] at hc
      exact Subtype.ext hc
    obtain ⟨c, rfl⟩ : ∃ c, a = fun _ => c := ⟨a i₀, funext ha⟩
    refine Or.inl (Or.inr ⟨L, L.period, ⟨L, rfl, isPrincipal_of_bases L b⟩, rfl, r,
      finrank ℂ (VirtualCharacter.rep c), coordinateRep (VirtualCharacter.rep c),
      LengthTwo.isIrreducible_of_equiv (coordinateEquiv _) (VirtualCharacter.isIrreducible_rep _),
      (hcusp i₀).of_equiv (coordinateEquiv _), b, L.layerReduction b,
      fun u i v hv => L.equivFun_layerReduction b u i v hv, inflationSmoothRep_eq_one _,
      isPairIsomorphic_inflationSmoothRep _⟩)

/-- **One step of the argument.** If `π` has a nonzero `U^1(𝓛)`-fixed vector, then `π` contains
a simple type or a split type of level `(0, 0)`, or `π` has a nonzero vector fixed by `U^1` of a
lattice chain of strictly larger period. -/
private theorem levelZero_step (ψF : AddChar F ℂ)
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (L : LatticeChain 𝒪[F] F (Fin n → F))
    {w : π} (hw : w ≠ 0)
    (hfix : ∀ g ∈ L.unitFiltration 1, π.representation ((toAut).symm g) w = w) :
    (∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      (IsGLSimpleType (n := n) ψF ρ ∨
        IsLevelZeroSplitType (V := Fin n → F) (glRepresentationToAut ρ))) ∨
    ∃ L' : LatticeChain 𝒪[F] F (Fin n → F), L.period < L'.period ∧
      ∃ w' : π, w' ≠ 0 ∧ ∀ g ∈ L'.unitFiltration 1, π.representation ((toAut).symm g) w' = w' := by
  classical
  let τ : Representation ℂ Aut π := π.representation.comp (toAut).symm.toMonoidHom
  have hfin : ∀ i : Fin L.period, Module.Finite (ResidueField 𝒪[F]) (L.Layer (i : ℕ)) := by
    intro i
    have : Module.Finite 𝒪[F] (L.lattice (i : ℕ)) := Module.Finite.iff_fg.mpr (L.fg_lattice _)
    exact Module.Finite.of_restrictScalars_finite 𝒪[F] _ _
  let b (i : Fin L.period) := Module.finBasis (ResidueField 𝒪[F]) (L.Layer (i : ℕ))
  obtain ⟨a, f, hf, hfτ⟩ := L.exists_layer_constituent b τ hw hfix
  by_cases hc : ∀ i, FiniteGeneralLinear.IsCuspidal (VirtualCharacter.rep (a i)).ρ
  · exact Or.inl (exists_type_of_cuspidal b a hc ψF π f hf hfτ)
  · push Not at hc
    obtain ⟨i₀, hi₀⟩ := hc
    have : ∀ i, Nontrivial (VirtualCharacter.rep (a i)) := fun i =>
      nontrivial_of_isIrreducible' (VirtualCharacter.isIrreducible_rep (a i))
    exact Or.inr (L.exists_refinement_of_not_isCuspidal b
      (fun i => (VirtualCharacter.rep (a i)).ρ) τ f hf hfτ i₀ hi₀)

end Matrix

/-- **BK93 (8.1.5), level zero.** An irreducible smooth representation of `GL_N(F)` with a
nonzero vector fixed by `U^1(𝔄)`, for some hereditary order `𝔄`, contains a simple type or a
split type of level `(0, 0)`. -/
theorem levelZeroTypeContainment : LevelZeroTypeContainmentStatement.{uF, uπ, uρ} := by
  intro F _ _ _ _ n _ ψF _ π _ hL
  suffices H : ∀ m : ℕ, ∀ L : LatticeChain 𝒪[F] F (Fin n → F), n - L.period = m →
      ∀ w : π, w ≠ 0 → (∀ g ∈ L.unitFiltration 1,
        π.representation ((Matrix.GeneralLinearGroup.toLin :
          GeneralLinear n F ≃* (Module.End F (Fin n → F))ˣ).symm g) w = w) →
      ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
        (IsGLSimpleType (n := n) ψF ρ ∨
          IsLevelZeroSplitType (V := Fin n → F) (glRepresentationToAut ρ)) by
    obtain ⟨L, w, hw, hfix⟩ := hL
    exact H _ L rfl w hw fun g hg => by simpa using hfix ⟨g, hg⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro L hm w hw hfix
    rcases levelZero_step ψF π L hw hfix with h | ⟨L', hlt, w', hw', hfix'⟩
    · exact h
    · have hle : L'.period ≤ n := by simpa using L'.period_le_card
      exact ih _ (by omega) L' rfl w' hw' hfix'

end Langlands.BushnellKutzko
