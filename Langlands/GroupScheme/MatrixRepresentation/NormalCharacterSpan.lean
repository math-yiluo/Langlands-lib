import Langlands.GroupScheme.MatrixRepresentation.CharacterSpaces
import Langlands.GroupScheme.MatrixRepresentation.RationalStableCoordinates
import Langlands.GroupScheme.NormalizedSubgroup
import Langlands.GroupScheme.InnerAutomorphism

/-! # Stability of the sum of normal-subgroup character spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}
  (i : H ⟶ G) [Mono i.hom.hom] (hN : (range i).IsNormal)

include hN in
omit [Mono i.hom.hom] in
/-- A normal subgroup is normalized by the identity homomorphism of its ambient group. -/
theorem isNormalizedBy_range_id : (range i).IsNormalizedBy (range (𝟙 G)) :=
  fun T g h _ hh => hN T g h (by trivial) hh

/-- Conjugation by a base point restricts to an actual automorphism of a normal subgroup. -/
def normalInnerIso (g : Over.mk (𝟙 S) ⟶ G.X) : H ≅ H :=
  isoOfPoints
    (fun T => normalizedConjAut i (𝟙 G) (isNormalizedBy_range_id i hN) T
      (G.constantPoint g T))
    (by
      intro T T' a h
      simpa only [normalizedConjAut_apply, GroupScheme.constantPoint_naturality] using
        (normalizedConjugation_naturality i (𝟙 G) (isNormalizedBy_range_id i hN)
          a (G.constantPoint g T) h).symm)

/-- The subgroup automorphism induces ambient conjugation on every test scheme. -/
theorem comp_normalInnerIso_hom_comp (g : Over.mk (𝟙 S) ⟶ G.X)
    (T : Over S) (h : T ⟶ H.X) :
    (h ≫ (normalInnerIso i hN g).hom.hom.hom) ≫ i.hom.hom =
      G.constantPoint g T * (h ≫ i.hom.hom) * (G.constantPoint g T)⁻¹ := by
  have hx : h ≫ (normalInnerIso i hN g).hom.hom.hom =
      normalizedConjAut i (𝟙 G) (isNormalizedBy_range_id i hN) T
        (G.constantPoint g T) h := comp_isoOfPoints_hom _ (by
      intro T T' a x
      simpa only [normalizedConjAut_apply, GroupScheme.constantPoint_naturality] using
        (normalizedConjugation_naturality i (𝟙 G) (isNormalizedBy_range_id i hN)
          a (G.constantPoint g T) x).symm) T h
  rw [hx, normalizedConjAut_apply, lift_comp_normalizedConjugation_comp]
  simp only [Grp.id_hom_hom, Category.comp_id]

end SubgroupFunctor

namespace MatrixRepresentation

section ConstantPoints

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix at a constant point is scalar extension of the rational-point matrix. -/
theorem pointMatrix_constantPoint (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X) (T : Over (Spec R)) :
    ρ.pointMatrix T (G.constantPoint g T) =
      Matrix.GeneralLinearGroup.map (scalarMap T) (ρ.rationalMatrix g) := by
  rw [constantPoint, pointMatrix_naturality]
  apply Units.ext
  ext r s
  let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  change T.hom.appTop.hom ((ρ.pointMatrix _ g).val r s) =
    T.hom.appTop.hom (e.symm (e ((ρ.pointMatrix _ g).val r s)))
  rw [e.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The constant-point matrix on an affine algebra uses its ordinary scalar map. -/
theorem affineMatrix_constantPoint (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X) (A : CommAlgCat.{u} R) :
    ρ.affineMatrix A (G.constantPoint g ((algSpec R).obj (op A))) =
      Matrix.GeneralLinearGroup.map (algebraMap R A) (ρ.rationalMatrix g) := by
  have h := ρ.pointMatrix_constantPoint g ((algSpec R).obj (op A))
  rw [pointMatrix_eq_affineMatrix] at h
  apply Units.ext
  ext r s
  let e : A →+* Γ(((algSpec R).obj (op A)).left, ⊤) :=
    (Corepresented.affineSectionsIso A).inv.hom.toRingHom
  have hi : Function.Injective e := by
    intro a b hab
    have hc := congrArg (Corepresented.affineSectionsIso A).hom.hom hab
    have hleft (a : A) : (Corepresented.affineSectionsIso A).hom.hom (e a) = a :=
      ConcreteCategory.congr_hom (Corepresented.affineSectionsIso A).inv_hom_id a
    exact (hleft a).symm.trans (hc.trans (hleft b))
  have he := congrArg (fun M : GL n Γ(((algSpec R).obj (op A)).left, ⊤) => M r s) h
  simp only [Matrix.GeneralLinearGroup.map_apply,
    UnipotentMatrixCriterion.scalarMap_affine] at he
  apply hi
  convert he using 1; rfl

end ConstantPoints

section CharacterSpan

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- The sum of all rational character spaces of an affine group representation. -/
def characterSpan (σ : MatrixRepresentation H n) : Submodule k (n → k) :=
  ⨆ χ, σ.characterSpace χ

variable (ρ : MatrixRepresentation G n) (i : H ⟶ G)
  [Mono i.hom.hom] (hN : (SubgroupFunctor.range i).IsNormal)

include hN in
/-- A rational ambient translate of a subgroup eigenvector belongs to a character
space for the conjugated actual subgroup character. -/
theorem exists_characterSpace_rational_translate
    {χ : rationalCharacters H} {v : n → k}
    (hv : v ∈ (ρ.restrict i).characterSpace χ)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ ψ : rationalCharacters H,
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ (ρ.restrict i).characterSpace ψ := by
  let f := (SubgroupFunctor.normalInnerIso i hN g⁻¹).hom
  let ψ := characterRestrict f χ
  refine ⟨ψ, ?_⟩
  let A := CharacterUnits.Coord H
  let x := CharacterUnits.universalPoint H
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let U := ρ.affineMatrix A (G.constantPoint g T)
  let M := (ρ.restrict i).affineMatrix A x
  let vA : n → A := fun r => algebraMap k A (v r)
  have hconst : G.constantPoint g⁻¹ T = (G.constantPoint g T)⁻¹ := by
    unfold constantPoint
    rw [GrpObj.comp_inv]
  have key := characterSpace_affine hv A (x ≫ f.hom.hom)
  rw [affineMatrix_restrict, SubgroupFunctor.comp_normalInnerIso_hom_comp,
    hconst, map_mul, map_mul, map_inv, inv_inv] at key
  have hψ : (Gm.affineUnitsEquiv (CommRingCat.of k) A
      ((x ≫ f.hom.hom) ≫ χ.toMul.hom.hom) : A) =
      (CharacterUnits.unit ψ : A) := by
    simp only [ψ, A, x, CharacterUnits.unit, characterRestrict_apply, Grp.comp_hom_hom,
      Category.assoc]
  rw [hψ] at key
  change ((U⁻¹ * M * U : GL n A) : Matrix n n A) *ᵥ vA =
    (CharacterUnits.unit ψ : A) • vA at key
  have hvec : (fun r => algebraMap k A (((ρ.rationalMatrix g : Matrix n n k) *ᵥ v) r)) =
      (U : Matrix n n A) *ᵥ vA := by
    rw [show U = Matrix.GeneralLinearGroup.map (algebraMap k A) (ρ.rationalMatrix g)
      from ρ.affineMatrix_constantPoint g A]
    funext r
    exact (algebraMap k A).map_mulVec _ _ r
  rw [mem_characterSpace_iff]
  change (M : Matrix n n A) *ᵥ
      (fun r => algebraMap k A (((ρ.rationalMatrix g : Matrix n n k) *ᵥ v) r)) = _
  rw [hvec]
  have he : (M : Matrix n n A) *ᵥ ((U : Matrix n n A) *ᵥ vA) =
      (U : Matrix n n A) *ᵥ
        (((U⁻¹ * M * U : GL n A) : Matrix n n A) *ᵥ vA) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [he, key, Matrix.mulVec_smul]

include hN in
/-- The sum of the subgroup character spaces is invariant on rational ambient points. -/
theorem rationalMatrix_mulVec_mem_characterSpan
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    {v : n → k} (hv : v ∈ (ρ.restrict i).characterSpan) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ (ρ.restrict i).characterSpan := by
  refine Submodule.iSup_induction (ρ.restrict i).characterSpace
    (motive := fun v => (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈
      (ρ.restrict i).characterSpan) hv ?_ ?_ ?_
  · intro χ v hv
    obtain ⟨ψ, hψ⟩ := exists_characterSpace_rational_translate ρ i hN hv g
    exact Submodule.mem_iSup_of_mem ψ hψ
  · simpa only [Matrix.mulVec_zero] using (ρ.restrict i).characterSpan.zero_mem
  · intro v w hv hw
    rw [Matrix.mulVec_add]
    exact (ρ.restrict i).characterSpan.add_mem hv hw

include hN in
/-- Split coordinates of the subgroup character span are invariant on all test
schemes when the ambient group is reduced and locally of finite type over an
algebraically closed field. The subgroup itself need not be reduced. -/
theorem isStableCoordinates_characterSpan [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]
    {m : Type} [Fintype m] (B : Matrix n m k) (C : Matrix m n k)
    (hcols : ∀ s, (fun r => B r s) ∈ (ρ.restrict i).characterSpan)
    (hproj : ∀ v, v ∈ (ρ.restrict i).characterSpan → (B * C) *ᵥ v = v) :
    ρ.IsStableCoordinates B C := by
  apply isStableCoordinates_of_rationalMatrix ρ B C
  intro g
  have he : (B * C) * ((ρ.rationalMatrix g : Matrix n n k) * B) =
      (ρ.rationalMatrix g : Matrix n n k) * B := by
    ext r s
    exact congrFun (hproj _ (rationalMatrix_mulVec_mem_characterSpan ρ i hN g (hcols s))) r
  simpa only [Matrix.mul_assoc] using he.symm

end CharacterSpan

end MatrixRepresentation

end Langlands.GroupScheme
