import Langlands.GroupScheme.ComponentConstantHom
import Langlands.GroupScheme.MatrixRepresentation.RationalIrreducibility

/-! # Componentwise constant matrix representations and their stable subspaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj
open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.ComponentConstant

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Rational points of the actual general linear group, in ground-field coordinates. -/
def generalLinearRationalEquiv :
    rationalPoints (GeneralLinear.groupScheme n (CommRingCat.of k)) ≃* GL n k :=
  (GeneralLinear.pointsEquiv n (CommRingCat.of k)
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).trans
      (Units.mapEquiv
        ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.mapMatrix).toMulEquiv)

theorem rationalMatrix_eq_generalLinearRationalEquiv
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation G n) (g : rationalPoints G) :
    ρ.rationalMatrix g = generalLinearRationalEquiv (g ≫ ρ.hom.hom) := rfl

variable [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom]

local instance : IsLocallyNoetherian G.X.left :=
  LocallyOfFiniteType.isLocallyNoetherian G.X.hom

/-- Algebraize a rational matrix homomorphism constant on actual components. -/
def ofComponentConstantRationalMatrix
    (r : rationalPoints G →* GL n k)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y) :
    MatrixRepresentation G n :=
  GroupScheme.ComponentConstant.ofRationalGroupHom G
    (GeneralLinear.groupScheme n (CommRingCat.of k))
    (generalLinearRationalEquiv.symm.toMonoidHom.comp r)
    (fun x y h => congrArg generalLinearRationalEquiv.symm (hr x y h))

@[simp] theorem rationalMatrix_ofComponentConstantRationalMatrix
    (r : rationalPoints G →* GL n k)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y)
    (g : rationalPoints G) :
    (ofComponentConstantRationalMatrix G r hr).rationalMatrix g = r g := by
  let r' := generalLinearRationalEquiv.symm.toMonoidHom.comp r
  have hr' : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r' x = r' y :=
    fun x y h => congrArg generalLinearRationalEquiv.symm (hr x y h)
  have hg := GroupScheme.ComponentConstant.comp_ofRationalGroupHom G
    (GeneralLinear.groupScheme n (CommRingCat.of k)) r' hr' g
  exact (congrArg generalLinearRationalEquiv hg).trans
    (generalLinearRationalEquiv.apply_symm_apply _)

theorem ofComponentConstantRationalMatrix_isComponentConstant
    (r : rationalPoints G →* GL n k)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y) :
    IsComponentConstant G.X (ofComponentConstantRationalMatrix G r hr).hom.hom :=
  GroupScheme.ComponentConstant.ofRationalGroupHom_isComponentConstant _ _ _ _

/-- On every actual open component scheme, a componentwise constant representation
has the scalar extension of its matrix at a rational component representative. -/
theorem pointMatrix_component
    (ρ : MatrixRepresentation G n) (hρ : IsComponentConstant G.X ρ.hom.hom)
    (c : _root_.ConnectedComponents G.X.left) :
    let T : Over (Spec (CommRingCat.of k)) :=
      Over.mk (componentι G.X.left c ≫ G.X.hom)
    let j : T ⟶ G.X := Over.homMk (componentι G.X.left c) rfl
    ρ.pointMatrix T j =
      Matrix.GeneralLinearGroup.map (scalarMap T)
        (ρ.rationalMatrix (representative G.X c)) := by
  dsimp only
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (componentι G.X.left c ≫ G.X.hom)
  let j : T ⟶ G.X := Over.homMk (componentι G.X.left c) rfl
  obtain ⟨s, hs⟩ := hρ
  have hre : representative G.X c ≫ ρ.hom.hom = s c := by
    rw [hs, section_comp_ofComponents, sectionComponent_representative]
  have hj : j ≫ ρ.hom.hom = toUnit T ≫ s c := by
    apply Over.OverMorphism.ext
    change componentι G.X.left c ≫ ρ.hom.hom.left =
      (componentι G.X.left c ≫ G.X.hom) ≫ (s c).left
    rw [hs, componentι_ofComponents]
    simp only [Category.assoc]
  calc
    ρ.pointMatrix T j =
        ρ.pointMatrix T (toUnit T ≫ representative G.X c) := by
      simp only [pointMatrix_apply, Category.assoc, hre, hj]
    _ = _ := pointMatrix_constant ρ (representative G.X c) T

omit [DecidableEq m] in
/-- For a componentwise constant representation, coordinate stability is detected
on rational matrices without any reducedness assumption. -/
theorem isStableCoordinates_of_componentConstant
    (ρ : MatrixRepresentation G n) (hρ : IsComponentConstant G.X ρ.hom.hom)
    (B : Matrix n m k) (C : Matrix m n k)
    (h : ∀ g : rationalPoints G, (ρ.rationalMatrix g : Matrix n n k) * B =
      B * (C * (ρ.rationalMatrix g : Matrix n n k) * B)) :
    ρ.IsStableCoordinates B C := by
  apply (stableCoordinates_iff_universal ρ B C).mpr
  have hlocal (c : _root_.ConnectedComponents G.X.left) :
      let T : Over (Spec (CommRingCat.of k)) :=
        Over.mk (componentι G.X.left c ≫ G.X.hom)
      let j : T ⟶ G.X := Over.homMk (componentι G.X.left c) rfl
      (ρ.pointMatrix T j : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) =
        B.map (scalarMap T) * (C.map (scalarMap T) *
          (ρ.pointMatrix T j : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T)) := by
    dsimp only
    rw [pointMatrix_component G ρ hρ c]
    let φ := scalarMap (Over.mk (componentι G.X.left c ≫ G.X.hom))
    change (ρ.rationalMatrix (representative G.X c) : Matrix n n k).map φ * B.map φ =
      B.map φ * (C.map φ *
        (ρ.rationalMatrix (representative G.X c) : Matrix n n k).map φ * B.map φ)
    simpa only [Matrix.map_mul] using
      congrArg (fun M : Matrix n m k => M.map φ) (h (representative G.X c))
  ext r s
  apply Scheme.OpenCover.ext_elem _ _ (componentOpenCover G.X.left)
  intro c
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (componentι G.X.left c ≫ G.X.hom)
  let j : T ⟶ G.X := Over.homMk (componentι G.X.left c) rfl
  have hB : (B.map (scalarMap G.X)).map j.left.appTop.hom = B.map (scalarMap T) := by
    ext a b
    exact scalarMap_comp j _
  have hC : (C.map (scalarMap G.X)).map j.left.appTop.hom = C.map (scalarMap T) := by
    ext a b
    exact scalarMap_comp j _
  have hM :
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)).map j.left.appTop.hom =
        (ρ.pointMatrix T j : Matrix n n Γ(T.left, ⊤)) := by
    have hj := congrArg Units.val (ρ.pointMatrix_naturality j (𝟙 G.X))
    change (ρ.pointMatrix T (j ≫ 𝟙 _) : Matrix n n Γ(T.left, ⊤)) =
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)).map j.left.appTop.hom at hj
    simpa only [Category.comp_id] using hj.symm
  change (((ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) *
      B.map (scalarMap G.X)).map j.left.appTop.hom) r s =
    ((B.map (scalarMap G.X) * (C.map (scalarMap G.X) *
      (ρ.pointMatrix G.X (𝟙 _) : Matrix n n Γ(G.X.left, ⊤)) *
        B.map (scalarMap G.X))).map j.left.appTop.hom) r s
  simpa only [Matrix.map_mul, hB, hC, hM] using
    congrArg (fun M => M r s) (hlocal c)

/-- Rationally stable subspaces of a componentwise constant representation are
stable on every affine test algebra. -/
theorem isStableSubspace_of_componentConstant
    (ρ : MatrixRepresentation G n) (hρ : IsComponentConstant G.X ρ.hom.hom)
    (V : Submodule k (n → k))
    (h : ∀ g v, v ∈ V → (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ V) :
    ρ.IsStableSubspace V := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates V
  have hstable : ρ.IsStableCoordinates B C := by
    apply isStableCoordinates_of_componentConstant G ρ hρ B C
    intro g
    have hmat : (B * C) * ((ρ.rationalMatrix g : Matrix n n k) * B) =
        (ρ.rationalMatrix g : Matrix n n k) * B := by
      ext r s
      exact congrFun (hproj _ (h g _ (hcols s))) r
    simpa only [Matrix.mul_assoc] using hmat.symm
  have hrange : LinearMap.range B.mulVecLin = V := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      exact mulVec_mem_of_columns hcols w
    · intro v hv
      exact ⟨C *ᵥ v, (Matrix.mulVec_mulVec v B C).trans (hproj v hv)⟩
  rw [← hrange]
  exact (intertwines_restrictCoordinates ρ B C hCB hstable).isStableSubspace_range

/-- For affine componentwise constant representations, all-test stability is
equivalent to stability under the rational matrices. -/
theorem isStableSubspace_iff_of_componentConstant [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (hρ : IsComponentConstant G.X ρ.hom.hom)
    (V : Submodule k (n → k)) :
    ρ.IsStableSubspace V ↔
      ∀ g v, v ∈ V → (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ V :=
  ⟨fun hV g _ hv => hV.rationalMatrix_mulVec_mem g hv,
    isStableSubspace_of_componentConstant G ρ hρ V⟩

/-- The algebraized representation has exactly the prescribed rationally stable
subspaces, with stability interpreted on every affine test. -/
theorem isStableSubspace_ofComponentConstantRationalMatrix_iff
    [IsAffineHom G.X.hom]
    (r : rationalPoints G →* GL n k)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y)
    (V : Submodule k (n → k)) :
    (ofComponentConstantRationalMatrix G r hr).IsStableSubspace V ↔
      ∀ g v, v ∈ V → (r g : Matrix n n k) *ᵥ v ∈ V := by
  constructor
  · intro hV g v hv
    have h := hV.rationalMatrix_mulVec_mem g hv
    rwa [rationalMatrix_ofComponentConstantRationalMatrix G r hr g] at h
  · intro hV
    apply isStableSubspace_of_componentConstant G
      (ofComponentConstantRationalMatrix G r hr)
      (ofComponentConstantRationalMatrix_isComponentConstant G r hr) V
    intro g v hv
    rw [rationalMatrix_ofComponentConstantRationalMatrix G r hr g]
    exact hV g v hv

end Langlands.GroupScheme.MatrixRepresentation
