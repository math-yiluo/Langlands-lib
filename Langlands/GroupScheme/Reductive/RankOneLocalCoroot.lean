import Langlands.GroupScheme.Reductive.RankOneRootCellWeyl
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralityPropagation
import Langlands.GroupScheme.Rational.KernelWeightImage
import Langlands.GroupScheme.Torus.CharacterMapHom
import Langlands.GroupScheme.Rational.RootFiniteness

/-! # The coroot of a rank-one open cell with a Weyl point

For cell data `D` (root groups of weights `±α` and an open triple cell, with `T` a split torus,
`i` a monomorphism, `α ≠ 0`, and `G` connected and locally of finite type) and a `k`-point `n`
normalizing `T` through an automorphism `σ` with `σ^* α = -α`, the scheme-theoretic kernel of
`α` centralizes the open cell, hence all of
`G`, hence commutes with `n`. Evaluating at the universal kernel point shows
`σ^* χ - χ ∈ ℤ α` for every character `χ`, which produces a cocharacter `h` with
`⟨α, h⟩ = 2` and `σ = 1 - α ≫ h`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneLocalCoroot

open RankOneRootCellRelation

variable {k : Type u} [Field k]

section Kernel

variable (D : CellData k) {Z : Over (Spec (CommRingCat.of k))}

/-- The root `α` is trivial on points of its scheme-theoretic kernel. -/
theorem cu_kernelPoint (c : Z ⟶ (RelativeRoot.characterKernel D.α).X) :
    cu D.α (c ≫ (RelativeRoot.characterKernelι D.α).hom.hom) = 1 := by
  have h : (c ≫ (RelativeRoot.characterKernelι D.α).hom.hom) ≫
      (CommGroupScheme.groupHom D.α).hom.hom = 1 := by
    rw [Category.assoc, (kernel_isPullback _).w, ← Category.assoc, comp_toUnit]
    rfl
  rw [cu, h, map_one]

/-- A torus point on which `α` is trivial commutes with every point of the open cell. -/
theorem commute_cellPt (s : Z ⟶ D.T.X) (hs : cu D.α s = 1) (y : Γ(Z.left, ⊤))
    (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) : Commute (D.I s) (D.cellPt y t x) := by
  have hB : Commute (D.I s) (D.B y) := by
    change D.I s * D.B y = D.B y * D.I s
    rw [CellData.I_mul_B, hs, inv_one, Units.val_one, one_mul]
  have hA : Commute (D.I s) (D.A x) := by
    change D.I s * D.A x = D.A x * D.I s
    rw [CellData.I_mul_A, hs, Units.val_one, one_mul]
  have hI : Commute (D.I s) (D.I t) := by
    change D.I s * D.I t = D.I t * D.I s
    rw [← CellData.I_mul, ← CellData.I_mul, mul_comm s t]
  exact hB.mul_right (hI.mul_right hA)

/-- The identity point of `G` lies in the open cell. -/
theorem identityPoint_mem_range_cellMul :
    IdentityComponent.identityPoint D.G ∈ Set.range D.cellMul.left := by
  have h1 : lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (Ga k).X)
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ D.T.X) 1) ≫ D.cellMul =
        η[D.G.X] := by
    rw [Dynamic.lift_tripleCellMultiplication, MonObj.one_comp D.xm.hom.hom,
      MonObj.one_comp D.i.hom.hom, MonObj.one_comp D.xp.hom.hom, one_mul, one_mul,
      Hom.one_def, toUnit_unit, Category.id_comp]
  refine ⟨(lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (Ga k).X)
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ D.T.X) 1)).left
        (IdentityComponent.basePoint k), ?_⟩
  have h2 := congrArg (fun f => f.left (IdentityComponent.basePoint k)) h1
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h2
  rw [h2]
  rfl

/-- **Kernel centrality.** In a connected group locally of finite type with an open cell,
points of the scheme-theoretic kernel of `α` commute with every point of `G`. -/
theorem commute_kernelPoint [LocallyOfFiniteType D.G.X.hom] [ConnectedSpace D.G.X.left]
    (c : Z ⟶ (RelativeRoot.characterKernel D.α).X) (g : Z ⟶ D.G.X) :
    Commute (D.I (c ≫ (RelativeRoot.characterKernelι D.α).hom.hom)) g := by
  have := D.open_cell
  have h := MultiplicativeTypeCentralityPropagation.commute_of_unitOpen
    (RelativeRoot.characterKernelι D.α ≫ D.i) D.cellMul
    (identityPoint_mem_range_cellMul D) ?_ Z c g
  · simpa only [CellData.I, Grp.comp_hom_hom, Category.assoc] using h
  · intro V a x
    obtain ⟨y, t, x', hyx⟩ := (D.inCell_iff (a ≫ D.cellMul)).mp ⟨a, rfl⟩
    rw [hyx]
    have := commute_cellPt D _ (cu_kernelPoint D x) y t x'
    simpa only [CellData.I, Grp.comp_hom_hom, Category.assoc] using this

end Kernel

section Normalizer

variable (D : CellData k) {Z : Over (Spec (CommRingCat.of k))}

/-- A point normalizing the torus fixes every point of the kernel of `α`. -/
theorem kernelPoint_comp_eq [LocallyOfFiniteType D.G.X.hom] [ConnectedSpace D.G.X.left]
    [Mono D.i.hom.hom] {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.G.X} {σ : D.T ≅ D.T}
    (hn : IsNormalizingPoint D.i n σ) (c : Z ⟶ (RelativeRoot.characterKernel D.α).X) :
    (c ≫ (RelativeRoot.characterKernelι D.α).hom.hom) ≫
        (CommGroupScheme.groupHom σ.hom).hom.hom =
      c ≫ (RelativeRoot.characterKernelι D.α).hom.hom := by
  let s := c ≫ (RelativeRoot.characterKernelι D.α).hom.hom
  have hconj := hn.conj_comp Z s
  have hc := (commute_kernelPoint D c (D.G.constantPoint n Z)).eq
  change (s ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) = s
  apply (cancel_mono D.i.hom.hom).mp
  rw [← hconj]
  change D.G.constantPoint n Z * D.I s * (D.G.constantPoint n Z)⁻¹ = D.I s
  rw [← hc, mul_inv_cancel_right]

end Normalizer

section Characters

variable (D : CellData k)

/-- **Integrality.** If a point `n` normalizes the torus through `σ`, then for every character
`χ` the difference `σ^* χ - χ` is an integral multiple of `α`. -/
theorem comp_sub_mem_zmultiples [LocallyOfFiniteType D.G.X.hom] [ConnectedSpace D.G.X.left]
    [Mono D.i.hom.hom] (hT : IsSplitTorus D.T.toGrp)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.G.X} {σ : D.T ≅ D.T}
    (hn : IsNormalizingPoint D.i n σ) (χ : characterLattice D.T) :
    σ.hom ≫ χ - χ ∈ AddSubgroup.zmultiples D.α := by
  let c₀ := Diagonalizable.kernelUniversalPoint D.T hT D.α
  let s₀ := c₀ ≫ (RelativeRoot.characterKernelι D.α).hom.hom
  have hfix : s₀ ≫ (CommGroupScheme.groupHom σ.hom).hom.hom = s₀ := kernelPoint_comp_eq D hn c₀
  have h0 : s₀ ≫ (CommGroupScheme.groupHom (σ.hom ≫ χ - χ)).hom.hom = 1 := by
    have hsub : s₀ ≫ (CommGroupScheme.groupHom (σ.hom ≫ χ - χ)).hom.hom =
        (s₀ ≫ (CommGroupScheme.groupHom (σ.hom ≫ χ)).hom.hom) *
          (s₀ ≫ (CommGroupScheme.groupHom χ).hom.hom)⁻¹ :=
      congrArg Additive.toMul ((evalPoint s₀).map_sub (σ.hom ≫ χ) χ)
    rw [hsub, comp_groupHom_comp, hfix, mul_inv_cancel]
  have hval : Lie.characterValue (σ.hom ≫ χ - χ) s₀ = 1 := by
    unfold Lie.characterValue
    erw [h0]
    exact map_one _
  rw [Diagonalizable.characterValue_kernelUniversalPoint] at hval
  exact (Diagonalizable.quotientUniversalCharacter_eq_one_iff (CommRingCat.of k) D.α _).mp hval

/-- **The coroot.** If moreover `σ^* α = -α` with `α ≠ 0`, then there is a cocharacter `h` with
`⟨α, h⟩ = 2` such that `σ` is the reflection `1 - α ≫ h`. -/
theorem exists_coroot [LocallyOfFiniteType D.G.X.hom] [ConnectedSpace D.G.X.left]
    [Mono D.i.hom.hom] (hT : IsSplitTorus D.T.toGrp) (hα : D.α ≠ 0)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.G.X} {σ : D.T ≅ D.T}
    (hn : IsNormalizingPoint D.i n σ) (hσ : σ.hom ≫ D.α = -D.α) :
    ∃ (h : cocharacterLattice D.T) (pair : latticePairing D.T D.α h = 2),
      σ = latticeReflectionIso D.α h pair := by
  classical
  have : IsAddTorsionFree (TensorProduct ℤ ℚ (characterLattice D.T)) :=
    IsAddTorsionFree.of_module_rat _
  have : IsAddTorsionFree (characterLattice D.T) :=
    hT.character_toRat_injective.isAddTorsionFree Langlands.LinearAlgebra.RationalSpan.toRat
  have hinj : Function.Injective (fun m : ℤ => m • D.α) := by
    intro a b hab
    have h0 : (a - b) • D.α = 0 := by
      simp only at hab
      rw [sub_smul, hab, sub_self]
    exact sub_eq_zero.mp ((IsAddTorsionFree.zsmul_eq_zero_iff_left hα).mp h0)
  have hex : ∀ χ : characterLattice D.T, ∃ m : ℤ, m • D.α = σ.hom ≫ χ - χ := fun χ =>
    AddSubgroup.mem_zmultiples_iff.mp (comp_sub_mem_zmultiples D hT hn χ)
  choose m hm using hex
  have hadd : ∀ χ ψ, m (χ + ψ) = m χ + m ψ := by
    intro χ ψ
    apply hinj
    simp only [add_smul, hm, Preadditive.comp_add]
    abel
  have hmα : m D.α = -2 := by
    apply hinj
    simp only [hm, hσ]
    rw [neg_smul, two_smul]
    abel
  let F : characterLattice D.T →+ characterLattice (Gm (Spec (CommRingCat.of k))) :=
    AddMonoidHom.mk' (fun χ => (-(m χ)) • 𝟙 (Gm (Spec (CommRingCat.of k)))) (fun χ ψ => by
      simp only [hadd, neg_add, add_smul])
  obtain ⟨t, ht⟩ := hT.exists_hom_of_characterMap F
  have pair : latticePairing D.T D.α t = 2 := by
    rw [latticePairing_apply, ht]
    change gmEndEquiv k ((-(m D.α)) • 𝟙 (Gm (Spec (CommRingCat.of k)))) = 2
    rw [gmEndEquiv_zsmul_id, hmα, neg_neg]
  refine ⟨t, pair, Iso.ext (hT.hom_ext_of_characters fun χ => ?_)⟩
  rw [latticeReflectionIso_hom, Preadditive.sub_comp, Category.id_comp, Category.assoc, ht]
  change σ.hom ≫ χ = χ - D.α ≫ ((-(m χ)) • 𝟙 (Gm (Spec (CommRingCat.of k))))
  rw [Preadditive.comp_zsmul, Category.comp_id, neg_smul, sub_neg_eq_add, hm]
  abel

end Characters

section Square

/-- If the torus represents the dynamic centralizer of some cocharacter `ν`, then the square of
a point normalizing the torus through an involution lies in the torus. -/
theorem exists_sq_eq_of_involution {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    {ν : cocharacterLattice T}
    (hC : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy i)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (hσ : σ.hom ≫ σ.hom = 𝟙 T) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X, n * n = z ≫ i.hom.hom := by
  have h2 : i ≫ (G.innerIso (n * n)).hom = i := by
    have h' := hn.mul hn
    rw [IsNormalizingPoint] at h'
    rw [h']
    have hσ' : (σ ≪≫ σ).hom = 𝟙 T := hσ
    rw [hσ']
    exact Category.id_comp i
  have hmem : n * n ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [Dynamic.mem_centralizer, Dynamic.orbit,
      comp_eq_constantPoint (fst _ (Gm (Spec (CommRingCat.of k))).X) (n * n)]
    let s := snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (Gm (Spec (CommRingCat.of k))).X ≫
      (CommGroupScheme.groupHom ν).hom.hom
    have hx := comp_innerIso_hom G (n * n) _ (s ≫ i.hom.hom)
    have hx' : (s ≫ i.hom.hom) ≫ (G.innerIso (n * n)).hom.hom.hom = s ≫ i.hom.hom := by
      rw [Category.assoc]
      exact congrArg (fun f : T.toGrp ⟶ G => s ≫ f.hom.hom) h2
    rw [hx'] at hx
    change (s ≫ i.hom.hom) * _ * (s ≫ i.hom.hom)⁻¹ = _
    rw [mul_inv_eq_iff_eq_mul]
    exact (mul_inv_eq_iff_eq_mul.mp hx.symm).symm
  exact ⟨(hC.pointsEquiv _).symm ⟨n * n, hmem⟩,
    (SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hC ⟨n * n, hmem⟩).symm⟩

end Square

end RankOneLocalCoroot

end Langlands.GroupScheme
