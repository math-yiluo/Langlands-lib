import Langlands.GroupScheme.Torus.GaloisLatticeRealizationStatement
import Langlands.GroupScheme.Torus.WeilRestrictionProductCharacters
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.KernelCocharacters
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Mathlib.RingTheory.Noetherian.Orzech

/-! # Realization of Galois lattices by tori: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace GaloisLatticeRealization

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]

/-- The constant family of top intermediate fields, indexed by `I`. -/
abbrev topFamily (I : Type u) : I → IntermediateField k L := fun _ => ⊤

/-- The coordinate set `I × Gal(L/k)` of the permutation lattice, in the form used by the
Weil restriction of `𝔾ₘ` from `∏_{i ∈ I} L`. -/
abbrev Coord (I : Type u) : Type u := Σ i, topFamily k L I i →ₐ[k] L

/-- The Galois automorphism attached to an embedding of the top intermediate field. -/
def gal (τ : (⊤ : IntermediateField k L) →ₐ[k] L) : L ≃ₐ[k] L :=
  (algEquivEquivAlgHom k L).symm (τ.comp (IntermediateField.topEquiv (F := k) (E := L)).symm.toAlgHom)

theorem gal_comp (σ : L ≃ₐ[k] L) (τ : (⊤ : IntermediateField k L) →ₐ[k] L) :
    gal k L (σ.toAlgHom.comp τ) = σ * gal k L τ := by
  apply (algEquivEquivAlgHom k L).injective
  rw [map_mul]
  simp only [gal, MulEquiv.apply_symm_apply]
  rfl

theorem gal_val : gal k L (⊤ : IntermediateField k L).val = 1 := by
  apply (algEquivEquivAlgHom k L).injective
  rw [map_one]
  simp only [gal, MulEquiv.apply_symm_apply]
  apply AlgHom.ext
  intro x
  rfl

variable {k L}

/-- The permutation representation of `Gal(L/k)` on `ℤ^(I × Gal(L/k))`, in the convention
of the Weil-restriction character formula: `(σ m)(i, τ) = m(i, σ⁻¹ τ)`. -/
def permRep (I : Type u) : Representation ℤ (L ≃ₐ[k] L) (Coord k L I → ℤ) where
  toFun σ := LinearMap.funLeft ℤ ℤ (fun j : Coord k L I => ⟨j.1, σ.symm.toAlgHom.comp j.2⟩)
  map_one' := by
    apply LinearMap.ext
    intro m
    funext j
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro m
    funext j
    rfl

omit [FiniteDimensional k L] in
theorem permRep_apply (I : Type u) (σ : L ≃ₐ[k] L) (m : Coord k L I → ℤ) (j : Coord k L I) :
    permRep I σ m j = m ⟨j.1, σ.symm.toAlgHom.comp j.2⟩ := rfl

variable {I : Type u} [Fintype I]

/-- Sending the coordinate `(i, τ)` to `gal(τ) • g i`. -/
def sumMap {V : Type u} [AddCommGroup V] (A : Representation ℤ (L ≃ₐ[k] L) V) (g : I → V) :
    (Coord k L I → ℤ) →ₗ[ℤ] V :=
  Fintype.linearCombination ℤ (fun j : Coord k L I => A (gal k L j.2) (g j.1))

theorem sumMap_permRep {V : Type u} [AddCommGroup V] (A : Representation ℤ (L ≃ₐ[k] L) V)
    (g : I → V) (σ : L ≃ₐ[k] L) (m : Coord k L I → ℤ) :
    sumMap A g (permRep I σ m) = A σ (sumMap A g m) := by
  let e : Coord k L I ≃ Coord k L I := WeilGm.productEmbeddingPermutation k L (topFamily k L I) σ
  simp only [sumMap, Fintype.linearCombination_apply, map_sum, map_zsmul]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro j _
  have h₁ : (σ.symm.toAlgHom.comp (σ.toAlgHom.comp j.2)) = j.2 := by
    apply AlgHom.ext
    intro x
    simp
  have h₂ : gal k L (σ.toAlgHom.comp j.2) = σ * gal k L j.2 := gal_comp k L σ j.2
  change m ⟨j.1, σ.symm.toAlgHom.comp (σ.toAlgHom.comp j.2)⟩ •
      A (gal k L (σ.toAlgHom.comp j.2)) (g j.1) = _
  rw [h₁, h₂, map_mul]
  rfl

open Classical in
theorem sumMap_single {V : Type u} [AddCommGroup V] (A : Representation ℤ (L ≃ₐ[k] L) V)
    (g : I → V) (i : I) :
    sumMap A g (Pi.single (⟨i, (⊤ : IntermediateField k L).val⟩ : Coord k L I) 1) = g i := by
  rw [sumMap, Fintype.linearCombination_apply_single, one_smul]
  change A (gal k L (⊤ : IntermediateField k L).val) (g i) = g i
  rw [gal_val, map_one]
  rfl

theorem sumMap_surjective_of_basis {V : Type u} [AddCommGroup V]
    (A : Representation ℤ (L ≃ₐ[k] L) V) (b : Module.Basis I ℤ V) :
    Function.Surjective (sumMap A b) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, sumMap_single A b i⟩

/-- The kernel of `sumMap` is the image of a map of the same shape out of another permutation
lattice: it is a finitely generated `ℤ`-module, stable under the action. -/
theorem exists_kernel_presentation {V : Type u} [AddCommGroup V]
    (A : Representation ℤ (L ≃ₐ[k] L) V) (g : I → V) :
    ∃ (I' : Type u) (_ : Fintype I') (g' : I' → (Coord k L I → ℤ)),
      LinearMap.range (sumMap (permRep I) g') = LinearMap.ker (sumMap A g) := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (LinearMap.ker (sumMap A g))
  refine ⟨s, inferInstance, fun x => (x : Coord k L I → ℤ), le_antisymm ?_ ?_⟩
  · rintro _ ⟨m, rfl⟩
    rw [LinearMap.mem_ker]
    change sumMap A g (∑ j, m j • permRep I (gal k L j.2) (j.1 : Coord k L I → ℤ)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_zsmul, sumMap_permRep]
    have hj : sumMap A g (j.1 : Coord k L I → ℤ) = 0 := by
      have h := Submodule.subset_span (R := ℤ) j.1.2
      rw [hs] at h
      exact h
    rw [hj, map_zero, smul_zero]
  · rw [← hs, Submodule.span_le]
    intro x hx
    exact ⟨_, sumMap_single (permRep I) (fun x : s => (x : Coord k L I → ℤ)) ⟨x, hx⟩⟩

variable (k L) [IsGalois k L]

/-- The permutation torus `Res_{(∏_{i ∈ I} L)/k} 𝔾ₘ`. -/
abbrev permTorus (I : Type u) [Fintype I] [DecidableEq I] :
    CommGroupScheme (Spec (CommRingCat.of k)) :=
  WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, topFamily k L I i)

theorem permTorus_isSplit (I : Type u) [Fintype I] [DecidableEq I] :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
      (permTorus k L I)).toGrp :=
  ⟨Coord k L I, inferInstance,
    ⟨WeilGm.decompositionIso (CommRingCat.of k) (CommRingCat.of L) (∀ i, topFamily k L I i)
      (Coord k L I) (WeilGm.productEmbeddingDecomposition k L (topFamily k L I))⟩⟩

theorem permTorus_equiv_galois (I : Type u) [Fintype I] [DecidableEq I] (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj
      (permTorus k L I))) :
    WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I)
        (characterLattice.galoisRepresentation k L (permTorus k L I) σ χ) =
      permRep I σ (WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I) χ) :=
  WeilGm.productEmbeddingCharacterEquiv_galoisRepresentation k L (topFamily k L I) σ χ

theorem permTorus_equiv_symm_galois (I : Type u) [Fintype I] [DecidableEq I]
    (σ : L ≃ₐ[k] L) (m : Coord k L I → ℤ) :
    characterLattice.galoisRepresentation k L (permTorus k L I) σ
        ((WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I)).symm m) =
      (WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I)).symm (permRep I σ m) :=
  WeilGm.galoisRepresentation_productEmbeddingCharacterEquiv_symm k L (topFamily k L I) σ m

end GaloisLatticeRealization

open GaloisLatticeRealization in
/-- Every free finite-rank `ℤ`-lattice with an action of `Gal(L/k)` is the character lattice
of a torus over `k` split by `L`, equivariantly. -/
theorem torusGaloisLatticeRealization : TorusGaloisLatticeRealizationStatement.{u} := by
  classical
  intro k L _ _ _ _ _ M _ _ _ ρ
  let I := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis I ℤ M := Module.Free.chooseBasis ℤ M
  let π : (Coord k L I → ℤ) →ₗ[ℤ] M := sumMap ρ b
  have hπ : Function.Surjective π := sumMap_surjective_of_basis ρ b
  obtain ⟨I', _, g', hg'⟩ := exists_kernel_presentation ρ b
  let f : (Coord k L I' → ℤ) →ₗ[ℤ] (Coord k L I → ℤ) := sumMap (permRep I) g'
  let R := permTorus k L I
  let R' := permTorus k L I'
  let bc := CommGroupScheme.baseChange (algebraBaseMap k L)
  have hR : IsSplitTorus (bc.obj R).toGrp := permTorus_isSplit k L I
  have hR' : IsSplitTorus (bc.obj R').toGrp := permTorus_isSplit k L I'
  let eR := WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I)
  let eR' := WeilGm.productEmbeddingCharacterEquiv k L (topFamily k L I')
  -- The equivariant character map between the permutation tori.
  let F : characterLattice (bc.obj R') →+ characterLattice (bc.obj R) :=
    eR.symm.toAddMonoidHom.comp (f.toAddMonoidHom.comp eR'.toAddMonoidHom)
  have hF : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (bc.obj R')),
      F (characterLattice.galoisRepresentation k L R' σ χ) =
        characterLattice.galoisRepresentation k L R σ (F χ) := by
    intro σ χ
    change eR.symm (f (eR' (characterLattice.galoisRepresentation k L R' σ χ))) =
      characterLattice.galoisRepresentation k L R σ (eR.symm (f (eR' χ)))
    rw [permTorus_equiv_galois k L I' σ χ, sumMap_permRep, permTorus_equiv_symm_galois]
  obtain ⟨φ, hφ, -⟩ := hR'.existsUnique_hom_of_equivariant_characterMap F hF
  -- The torus: the kernel of `φ`.
  let T := CommGroupScheme.kernel φ
  let φL := bc.map φ
  let θ : characterLattice (bc.obj R) →+ M := π.toAddMonoidHom.comp eR.toAddMonoidHom
  have hθ : Function.Surjective θ := by
    intro m
    obtain ⟨p, rfl⟩ := hπ m
    refine ⟨eR.symm p, ?_⟩
    change π (eR (eR.symm p)) = π p
    rw [AddEquiv.apply_symm_apply]
  have hθσ : ∀ (σ : L ≃ₐ[k] L) (χ : characterLattice (bc.obj R)),
      θ (characterLattice.galoisRepresentation k L R σ χ) = ρ σ (θ χ) := by
    intro σ χ
    change π (eR (characterLattice.galoisRepresentation k L R σ χ)) = ρ σ (π (eR χ))
    rw [permTorus_equiv_galois k L I σ χ]
    exact sumMap_permRep ρ b σ (eR χ)
  have hker : (characterLattice.comapHom (CommGroupScheme.groupHom φL)).range = θ.ker := by
    ext χ
    constructor
    · rintro ⟨χ', rfl⟩
      rw [AddMonoidHom.mem_ker]
      have h₁ : characterLattice.comapHom (CommGroupScheme.groupHom φL) χ' = F χ' := hφ χ'
      rw [h₁]
      change π (eR (eR.symm (f (eR' χ')))) = 0
      rw [AddEquiv.apply_symm_apply, ← LinearMap.mem_ker, ← hg']
      exact LinearMap.mem_range_self f _
    · intro hχ
      rw [AddMonoidHom.mem_ker] at hχ
      have h₂ : eR χ ∈ LinearMap.range f := by
        rw [hg', LinearMap.mem_ker]
        exact hχ
      obtain ⟨p', hp'⟩ := h₂
      refine ⟨eR'.symm p', ?_⟩
      have h₁ : characterLattice.comapHom (CommGroupScheme.groupHom φL) (eR'.symm p') =
          F (eR'.symm p') := hφ _
      rw [h₁]
      change eR.symm (f (eR' (eR'.symm p'))) = χ
      rw [AddEquiv.apply_symm_apply, hp', AddEquiv.symm_apply_apply]
  -- The base change of `T` is the diagonalizable group of `M`, hence split.
  let iso1 := CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k L) φ
  let i1 : (bc.obj T).toGrp ≅ GroupScheme.kernel (CommGroupScheme.groupHom φL) :=
    ⟨CommGroupScheme.groupHom iso1.hom, CommGroupScheme.groupHom iso1.inv,
      congrArg CommGroupScheme.groupHom iso1.hom_inv_id,
      congrArg CommGroupScheme.groupHom iso1.inv_hom_id⟩
  let ΛM : Diagonalizable.homKernelLattice (CommGroupScheme.groupHom φL) ≃+ M :=
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective θ hθ)
  let cΛ : Diagonalizable.homKernelLattice (CommGroupScheme.groupHom φL) ≃+ (I → ℤ) :=
    ΛM.trans b.equivFun.toAddEquiv
  let eTL : (bc.obj T).toGrp ≅ splitTorus (Spec (CommRingCat.of L)) I :=
    i1 ≪≫ Diagonalizable.homKernelDiagonalizableIso (CommGroupScheme.groupHom φL) hR hR' ≪≫
      Diagonalizable.splitIso (CommRingCat.of L) cΛ
  have hTL : IsSplitTorus (bc.obj T).toGrp := ⟨I, inferInstance, ⟨eTL⟩⟩
  let cT : characterLattice (bc.obj T) ≃+ (I → ℤ) :=
    (characterLattice.congr (CommGroupScheme.isoOfGroupIso
      (U := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I) eTL)).trans
      (splitTorus.characterLatticeEquiv L I)
  -- Restriction of characters along the inclusion.
  let ι := bc.map (CommGroupScheme.kernelι φ)
  have hι : ι = iso1.hom ≫ CommGroupScheme.kernelι φL :=
    (CommGroupScheme.kernelBaseChangeIso_hom_ι (algebraBaseMap k L) φ).symm
  let ψ : characterLattice (bc.obj R) →+ characterLattice (bc.obj T) :=
    characterLattice.precompose ι
  have hψ : Function.Surjective ψ := by
    have h₁ : Mono ((Over.pullback (algebraBaseMap k L)).map
        (GroupScheme.kernelι (CommGroupScheme.groupHom φ)).hom.hom) := inferInstance
    have h₂ : Mono (CommGroupScheme.groupHom ι).hom.hom := h₁
    have : Mono (CommGroupScheme.groupHom ι).hom.hom.left := inferInstance
    intro χ
    obtain ⟨χ', hχ'⟩ :=
      IsSplitTorus.characterRestrict_surjective_of_mono hTL hR (CommGroupScheme.groupHom ι) χ
    exact ⟨χ', hχ'⟩
  have hιφ : ι ≫ φL = 0 := by
    rw [hι, Category.assoc, CommGroupScheme.kernelι_comp, Limits.comp_zero]
  have hψθ : θ.ker ≤ ψ.ker := by
    intro χ hχ
    rw [← hker] at hχ
    obtain ⟨χ', rfl⟩ := hχ
    rw [AddMonoidHom.mem_ker]
    change ι ≫ (φL ≫ χ') = 0
    rw [← Category.assoc, hιφ, Limits.zero_comp]
  let qθ := QuotientAddGroup.quotientKerEquivOfSurjective θ hθ
  let ψb : M →+ characterLattice (bc.obj T) :=
    (QuotientAddGroup.lift θ.ker ψ hψθ).comp qθ.symm.toAddMonoidHom
  have hψb : ∀ χ, ψb (θ χ) = ψ χ := by
    intro χ
    have hq : qθ.symm (θ χ) = (QuotientAddGroup.mk χ : characterLattice (bc.obj R) ⧸ θ.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    change QuotientAddGroup.lift θ.ker ψ hψθ (qθ.symm (θ χ)) = ψ χ
    rw [hq]
    rfl
  have hψb_surj : Function.Surjective ψb := by
    intro y
    obtain ⟨χ, rfl⟩ := hψ y
    exact ⟨θ χ, hψb χ⟩
  have hψb_inj : Function.Injective ψb := by
    let E : (I → ℤ) →+ (I → ℤ) :=
      cT.toAddMonoidHom.comp (ψb.comp b.equivFun.symm.toAddEquiv.toAddMonoidHom)
    have hE : Function.Surjective E := by
      intro y
      obtain ⟨m, hm⟩ := hψb_surj (cT.symm y)
      refine ⟨b.equivFun m, ?_⟩
      change cT (ψb (b.equivFun.symm (b.equivFun m))) = y
      rw [LinearEquiv.symm_apply_apply, hm, AddEquiv.apply_symm_apply]
    have hEi : Function.Injective E :=
      IsNoetherian.injective_of_surjective_endomorphism E.toIntLinearMap hE
    intro m m' h
    apply b.equivFun.injective
    apply hEi
    change cT (ψb (b.equivFun.symm (b.equivFun m))) =
      cT (ψb (b.equivFun.symm (b.equivFun m')))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]
  let e : M ≃+ characterLattice (bc.obj T) := AddEquiv.ofBijective ψb ⟨hψb_inj, hψb_surj⟩
  refine ⟨T, e, hTL, ?_⟩
  intro σ m
  obtain ⟨χ, rfl⟩ := hθ m
  change ψb (ρ σ (θ χ)) = characterLattice.galoisRepresentation k L T σ (ψb (θ χ))
  rw [← hθσ, hψb, hψb]
  exact (characterLattice.galoisRepresentation_precompose k L (CommGroupScheme.kernelι φ) σ χ).symm

end Langlands.GroupScheme
