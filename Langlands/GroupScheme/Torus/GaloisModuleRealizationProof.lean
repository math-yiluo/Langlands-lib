import Langlands.GroupScheme.Torus.GaloisModuleRealizationStatement
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof

/-! # Realization of Galois modules by groups of multiplicative type: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace GaloisModuleRealization

open GaloisLatticeRealization

/-- `sumMap A g` is surjective as soon as the family `g` spans. -/
theorem sumMap_surjective_of_span {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] {I : Type u} [Fintype I] {V : Type u} [AddCommGroup V]
    (A : Representation ℤ (L ≃ₐ[k] L) V) (g : I → V)
    (hg : Submodule.span ℤ (Set.range g) = ⊤) :
    Function.Surjective (sumMap A g) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, sumMap_single A g i⟩

section Congr

variable (R : CommRingCat.{u}) {Λ M : Type u} [AddCommGroup Λ] [AddCommGroup M]

/-- Restriction of `M`-valued characters along a change of test scheme. -/
def charRestrict {U U' : Over (Spec R)} (a : U' ⟶ U) :
    (Multiplicative M →* (Γ(U.left, ⊤))ˣ) →* (Multiplicative M →* (Γ(U'.left, ⊤))ˣ) :=
  MonoidHom.compHom (Units.map a.left.appTop.hom.toMonoidHom)

/-- Points of `D(Λ)`, read as characters of `M` through `c : Λ ≃+ M`. -/
def congrPointsEquiv (c : Λ ≃+ M) (U : Over (Spec R)) :
    (U ⟶ (Diagonalizable.groupScheme R Λ).X) ≃* (Multiplicative M →* (Γ(U.left, ⊤))ˣ) :=
  (Diagonalizable.characterPointsEquiv R Λ U).trans
    (MulEquiv.monoidHomCongrLeft (AddEquiv.toMultiplicative c))

theorem congrPointsEquiv_apply (c : Λ ≃+ M) (U : Over (Spec R))
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) (m : M) :
    congrPointsEquiv R c U x (.ofAdd m) =
      Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd (c.symm m)) :=
  rfl

theorem congrPointsEquiv_naturality (c : Λ ≃+ M) {U U' : Over (Spec R)} (a : U' ⟶ U)
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) :
    congrPointsEquiv R c U' (a ≫ x) = charRestrict R a (congrPointsEquiv R c U x) := by
  apply MonoidHom.ext
  intro m
  exact Diagonalizable.characterPointsEquiv_naturality R Λ a x (c.symm m.toAdd)

theorem characterPointsEquiv_naturality' {U U' : Over (Spec R)} (a : U' ⟶ U)
    (y : U ⟶ (Diagonalizable.groupScheme R M).X) :
    Diagonalizable.characterPointsEquiv R M U' (a ≫ y) =
      charRestrict R a (Diagonalizable.characterPointsEquiv R M U y) := by
  apply MonoidHom.ext
  intro m
  exact Diagonalizable.characterPointsEquiv_naturality R M a y m.toAdd

/-- An additive isomorphism `c : Λ ≃+ M` gives `D(Λ) ≅ D(M)`. -/
def diagCongr (c : Λ ≃+ M) :
    (Diagonalizable.groupScheme R Λ).toGrp ≅ (Diagonalizable.groupScheme R M).toGrp :=
  isoOfPointModels (fun U : Over (Spec R) => Multiplicative M →* (Γ(U.left, ⊤))ˣ)
    (fun a => charRestrict R a) (congrPointsEquiv R c)
    (Diagonalizable.characterPointsEquiv R M)
    (congrPointsEquiv_naturality R c) (characterPointsEquiv_naturality' R)

/-- On points, `D(Λ) ≅ D(M)` evaluates at `m` as the original point evaluates at `c⁻¹ m`. -/
theorem diagCongr_hom (c : Λ ≃+ M) (U : Over (Spec R))
    (x : U ⟶ (Diagonalizable.groupScheme R Λ).X) (m : M) :
    Diagonalizable.characterPointsEquiv R M U (x ≫ (diagCongr R c).hom.hom.hom) (.ofAdd m) =
      Diagonalizable.characterPointsEquiv R Λ U x (.ofAdd (c.symm m)) := by
  have h := isoOfPointModels_hom
    (fun U : Over (Spec R) => Multiplicative M →* (Γ(U.left, ⊤))ˣ)
    (fun a => charRestrict R a) (congrPointsEquiv R c)
    (Diagonalizable.characterPointsEquiv R M)
    (congrPointsEquiv_naturality R c) (characterPointsEquiv_naturality' R) U x
  exact congrArg (fun χ : Multiplicative M →* (Γ(U.left, ⊤))ˣ => χ (.ofAdd m)) h

end Congr

/-- Points move back and forth along an isomorphism of commutative group schemes. -/
theorem comp_inv_hom {S : Scheme.{u}} {G H : CommGroupScheme S} (e : G ≅ H) {U : Over S}
    (y : U ⟶ H.X) :
    (y ≫ (CommGroupScheme.groupHom e.inv).hom.hom) ≫ (CommGroupScheme.groupHom e.hom).hom.hom =
      y := by
  rw [← comp_groupHom_comp, e.inv_hom_id]
  rfl

theorem comp_hom_inv {S : Scheme.{u}} {G H : CommGroupScheme S} (e : G ≅ H) {U : Over S}
    (x : U ⟶ G.X) :
    (x ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫ (CommGroupScheme.groupHom e.inv).hom.hom =
      x := by
  rw [← comp_groupHom_comp, e.hom_inv_id]
  rfl

/-- The realization, assuming the description of the characters of diagonalizable groups. -/
theorem realization_of_diagonalizableCharacter
    (hD : DiagonalizableCharacterStatement.{u}) :
    MultiplicativeTypeGaloisModuleRealizationStatement.{u} := by
  classical
  intro k L _ _ _ _ _ M _ _ ρ
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ M).FG)
  let I : Type u := S
  let g : I → M := fun i => (i : M)
  have hg : Submodule.span ℤ (Set.range g) = ⊤ := by
    rw [← hS]
    congr 1
    ext x
    simp [g, I]
  let π : (Coord k L I → ℤ) →ₗ[ℤ] M := sumMap ρ g
  have hπ : Function.Surjective π := sumMap_surjective_of_span ρ g hg
  obtain ⟨I', _, g', hg'⟩ := exists_kernel_presentation ρ g
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
  -- The group of multiplicative type: the kernel of `φ`.
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
    exact sumMap_permRep ρ g σ (eR χ)
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
  -- The base change of `T` is the diagonalizable group of `M`.
  let iso1 := CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k L) φ
  let i1 : (bc.obj T).toGrp ≅ GroupScheme.kernel (CommGroupScheme.groupHom φL) :=
    ⟨CommGroupScheme.groupHom iso1.hom, CommGroupScheme.groupHom iso1.inv,
      congrArg CommGroupScheme.groupHom iso1.hom_inv_id,
      congrArg CommGroupScheme.groupHom iso1.inv_hom_id⟩
  let ΛM : Diagonalizable.homKernelLattice (CommGroupScheme.groupHom φL) ≃+ M :=
    (QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective θ hθ)
  have hΛM : ∀ χ : characterLattice (bc.obj R),
      ΛM.symm (θ χ) = Diagonalizable.subgroupQuotientMap
        (characterLattice.comapHom (CommGroupScheme.groupHom φL)).range χ := by
    intro χ
    rw [AddEquiv.symm_apply_eq]
    rfl
  let hk := Diagonalizable.homKernelDiagonalizableIso (CommGroupScheme.groupHom φL) hR hR'
  let iG : (bc.obj T).toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of L) M).toGrp :=
    i1 ≪≫ hk ≪≫ diagCongr (CommRingCat.of L) ΛM
  let i : bc.obj T ≅ Diagonalizable.groupScheme (CommRingCat.of L) M :=
    CommGroupScheme.isoOfGroupIso iG
  -- Restriction of characters along the inclusion.
  let ιT := bc.map (CommGroupScheme.kernelι φ)
  have hιT : ιT = iso1.hom ≫ CommGroupScheme.kernelι φL :=
    (CommGroupScheme.kernelBaseChangeIso_hom_ι (algebraBaseMap k L) φ).symm
  let ψ : characterLattice (bc.obj R) →+ characterLattice (bc.obj T) :=
    characterLattice.precompose ιT
  have hιTφ : ιT ≫ φL = 0 := by
    rw [hιT, Category.assoc, CommGroupScheme.kernelι_comp, Limits.comp_zero]
  have hψθ : θ.ker ≤ ψ.ker := by
    intro χ hχ
    rw [← hker] at hχ
    obtain ⟨χ', rfl⟩ := hχ
    rw [AddMonoidHom.mem_ker]
    change ιT ≫ (φL ≫ χ') = 0
    rw [← Category.assoc, hιTφ, Limits.zero_comp]
  let qθ := QuotientAddGroup.quotientKerEquivOfSurjective θ hθ
  let ψb : M →+ characterLattice (bc.obj T) :=
    (QuotientAddGroup.lift θ.ker ψ hψθ).comp qθ.symm.toAddMonoidHom
  have hψb : ∀ χ, ψb (θ χ) = ψ χ := by
    intro χ
    have hq : qθ.symm (θ χ) =
        (QuotientAddGroup.mk χ : characterLattice (bc.obj R) ⧸ θ.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    change QuotientAddGroup.lift θ.ker ψ hψθ (qθ.symm (θ χ)) = ψ χ
    rw [hq]
    rfl
  -- The value of `ψb m` at a point is the evaluation at `m` of its image in `D(M)`.
  have hval : ∀ (m : M) (U : Over (Spec (CommRingCat.of L)))
      (x : U ⟶ (bc.obj T).X),
      Gm.pointsEquiv _ U (x ≫ (CommGroupScheme.groupHom (ψb m)).hom.hom) =
        Diagonalizable.characterPointsEquiv (CommRingCat.of L) M U
          (x ≫ (CommGroupScheme.groupHom i.hom).hom.hom) (Multiplicative.ofAdd m) := by
    intro m U x
    obtain ⟨χ, rfl⟩ := hθ m
    rw [hψb]
    let z := (x ≫ i1.hom.hom.hom) ≫ hk.hom.hom.hom
    have hz : z ≫ hk.inv.hom.hom = x ≫ i1.hom.hom.hom := by
      simp only [z, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Category.comp_id]
    have hx : x ≫ (CommGroupScheme.groupHom ιT).hom.hom =
        (z ≫ hk.inv.hom.hom) ≫
          (GroupScheme.kernelι (CommGroupScheme.groupHom φL)).hom.hom := by
      rw [hz, hιT]
      rfl
    have hxi : x ≫ (CommGroupScheme.groupHom i.hom).hom.hom =
        z ≫ (diagCongr (CommRingCat.of L) ΛM).hom.hom.hom := by
      simp only [z, Category.assoc]
      rfl
    change Gm.pointsEquiv _ U ((x ≫ (CommGroupScheme.groupHom ιT).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = _
    rw [hx, hxi, diagCongr_hom, Diagonalizable.homKernelDiagonalizableIso_inv, hΛM]
  -- Bijectivity from the description of the characters of `D(M)`.
  obtain ⟨-, h1b⟩ := (hD L).1 M
  have hψb_inj : Function.Injective ψb := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨m₀, -, huniq⟩ := h1b 0
    have h0 : (0 : M) = m₀ := by
      apply huniq
      intro U y
      rw [comp_groupHom_zero, map_one, ofAdd_zero, map_one]
    have hm₀ : m = m₀ := by
      apply huniq
      intro U y
      rw [comp_groupHom_zero, map_one]
      have h := hval m U (y ≫ (CommGroupScheme.groupHom i.inv).hom.hom)
      rw [hm, comp_groupHom_zero, map_one, comp_inv_hom] at h
      exact h
    rw [hm₀, ← h0]
  have hψb_surj : Function.Surjective ψb := by
    intro χ
    obtain ⟨m, hm, -⟩ := h1b (i.inv ≫ χ)
    refine ⟨m, CommGroupScheme.hom_ext_points fun U x => ?_⟩
    apply (Gm.pointsEquiv _ U).injective
    rw [hval m U x, ← hm U (x ≫ (CommGroupScheme.groupHom i.hom).hom.hom),
      comp_groupHom_comp, comp_hom_inv]
  let e : M ≃+ characterLattice (bc.obj T) := AddEquiv.ofBijective ψb ⟨hψb_inj, hψb_surj⟩
  refine ⟨T, i, e, fun m U x => hval m U x, ?_⟩
  intro σ m
  obtain ⟨χ, rfl⟩ := hθ m
  change ψb (ρ σ (θ χ)) = characterLattice.galoisRepresentation k L T σ (ψb (θ χ))
  rw [← hθσ, hψb, hψb]
  exact (characterLattice.galoisRepresentation_precompose k L (CommGroupScheme.kernelι φ) σ χ).symm

end GaloisModuleRealization

/-- Every finitely generated Galois module `M` for a finite Galois extension `L/k` is the
character module of a commutative group scheme over `k` that becomes diagonalizable over `L`. -/
theorem multiplicativeTypeGaloisModuleRealization :
    MultiplicativeTypeGaloisModuleRealizationStatement.{u} :=
  GaloisModuleRealization.realization_of_diagonalizableCharacter diagonalizableCharacter

end Langlands.GroupScheme
