import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates

/-! # Coarser block Levi projections on block unipotent subgroups of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

section Matrix

variable {A : Type*} [CommRing A] {e w : n → ℤ} (hw : ∀ i j, e i ≤ e j → w i ≤ w j)

include hw

/-- The block unipotent subgroup of a coarser weight lies in that of the finer weight. -/
theorem blockUnipotentSubgroup_le_of_le :
    blockUnipotentSubgroup A w ≤ blockUnipotentSubgroup A e :=
  fun _ hg i j hij => hg i j (hw i j hij)

/-- The block unipotent subgroup of the finer weight lies in the block parabolic subgroup of
the coarser weight. -/
theorem blockUnipotentSubgroup_le_blockParabolicSubgroup_of_le :
    blockUnipotentSubgroup A e ≤ blockParabolicSubgroup A w := by
  intro g hg i j hij
  have hlt : e i < e j := lt_of_not_ge fun h => hij.not_ge (hw j i h)
  rw [hg i j hlt.le]
  exact Matrix.one_apply_ne fun h => hlt.ne (congrArg e h)

/-- The coarser block diagonal part of a finer block unipotent matrix is again finer block
unipotent, and it is block diagonal for the coarser weight. -/
theorem blockLeviProjection_mem_of_le (g : GL n A) (hg : g ∈ blockUnipotentSubgroup A e) :
    blockLeviProjection A w ⟨g, blockUnipotentSubgroup_le_blockParabolicSubgroup_of_le hw hg⟩ ∈
      blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · change blockDiagonalPart A w (g : Matrix n n A) i j = _
    rw [blockDiagonalPart_apply]
    split_ifs with h
    · exact hg i j hij
    · exact (Matrix.one_apply_ne fun h' => h (congrArg w h')).symm
  · change blockDiagonalPart A w (g : Matrix n n A) i j = 0
    rw [blockDiagonalPart_apply, ite_eq_right hij]

variable (A) in
/-- The coarser block diagonal part on the finer block unipotent subgroup. -/
def unipotentLeviProjection :
    blockUnipotentSubgroup A e →* ↥(blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w) :=
  ((blockLeviProjection A w).comp (Subgroup.inclusion
    (blockUnipotentSubgroup_le_blockParabolicSubgroup_of_le (A := A) hw))).codRestrict
    _ fun g => blockLeviProjection_mem_of_le hw g.val g.property

theorem coe_unipotentLeviProjection (g : blockUnipotentSubgroup A e) :
    ((unipotentLeviProjection A hw g : GL n A) : Matrix n n A) =
      blockDiagonalPart A w ((g : GL n A) : Matrix n n A) :=
  rfl

/-- The projection is the identity on coarser block diagonal elements. -/
theorem unipotentLeviProjection_of_mem (g : GL n A)
    (hg : g ∈ blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w) :
    (unipotentLeviProjection A hw ⟨g, hg.1⟩ : GL n A) = g := by
  apply Units.ext
  ext i j
  rw [coe_unipotentLeviProjection, blockDiagonalPart_apply]
  split_ifs with h
  · rfl
  · exact (hg.2 i j h).symm

/-- The kernel of the projection is the coarser block unipotent subgroup. -/
theorem unipotentLeviProjection_eq_one_iff (g : blockUnipotentSubgroup A e) :
    unipotentLeviProjection A hw g = 1 ↔ (g : GL n A) ∈ blockUnipotentSubgroup A w := by
  rw [mem_blockUnipotentSubgroup, blockUnipotent_iff]
  constructor
  · intro h
    refine ⟨blockUnipotentSubgroup_le_blockParabolicSubgroup_of_le hw g.property, ?_⟩
    have := congrArg (fun x : ↥(blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w) =>
      ((x : GL n A) : Matrix n n A)) h
    simpa [coe_unipotentLeviProjection] using this
  · rintro ⟨-, h⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_unipotentLeviProjection, h]
    rfl

/-- The projection commutes with change of coefficients. -/
theorem map_unipotentLeviProjection {B : Type*} [CommRing B] (f : A →+* B)
    (g : blockUnipotentSubgroup A e) :
    Matrix.GeneralLinearGroup.map f (unipotentLeviProjection A hw g : GL n A) =
      unipotentLeviProjection B hw
        ⟨Matrix.GeneralLinearGroup.map f g.val, map_mem_blockUnipotentSubgroup e f g.property⟩ := by
  apply Units.ext
  ext i j
  rw [coe_unipotentLeviProjection, blockDiagonalPart_apply]
  change f (blockDiagonalPart A w ((g : GL n A) : Matrix n n A) i j) = _
  rw [blockDiagonalPart_apply]
  split_ifs
  · rfl
  · exact map_zero f

section Topology

variable [TopologicalSpace A]

omit hw [Fintype n] [DecidableEq n] in
/-- Taking a block diagonal part is continuous for the entrywise topology. -/
theorem continuous_blockDiagonalPart (v : n → ℤ) : Continuous (blockDiagonalPart A v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun M : Matrix n n A => if v i = v j then M i j else 0
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

/-- The coarser block Levi projection is continuous for the matrix-units topology. -/
theorem continuous_unipotentLeviProjection : Continuous (unipotentLeviProjection A hw) := by
  refine continuous_induced_rng.mpr (Units.continuous_iff.mpr ⟨?_, ?_⟩)
  · exact (continuous_blockDiagonalPart w).comp (Units.continuous_val.comp continuous_subtype_val)
  · exact (continuous_blockDiagonalPart w).comp
      (Units.continuous_coe_inv.comp continuous_subtype_val)

end Topology

end Matrix

section Points

variable (R : CommRingCat.{u})

/-- On an affine test scheme, membership in a matrix-subgroup functor is membership of the
affine coefficient matrix. -/
theorem mem_ofMatrixSubgroups_affinePoints_iff {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    (S : CommAlgCat.{u} R) (x : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    x ∈ (ofMatrixSubgroups (R := R) H hH).carrier ((algSpec R).obj (op S)) ↔
      affinePointsEquiv n R S x ∈ H (CommRingCat.of S) := by
  rw [mem_ofMatrixSubgroups, pointsEquiv_eq_affinePointsEquiv]
  constructor
  · intro hx
    have h := hH (CommRingCat.ofHom (Corepresented.affineSectionsIso S).hom.hom.toRingHom) hx
    convert h using 1
    apply Units.ext
    ext i j
    exact (congrArg (fun f : S ⟶ S => f.hom ((affinePointsEquiv n R S x : Matrix n n S) i j))
      (Corepresented.affineSectionsIso S).inv_hom_id).symm
  · intro hx
    exact hH (CommRingCat.ofHom (Corepresented.affineSectionsIso S).inv.hom.toRingHom) hx

/-- Affine points of a matrix-subgroup functor are the matrices of the subgroup. -/
def ofMatrixSubgroupsAffineEquiv {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    (S : CommAlgCat.{u} R) :
    (ofMatrixSubgroups (R := R) H hH).carrier ((algSpec R).obj (op S)) ≃* H (CommRingCat.of S) where
  toFun x := ⟨affinePointsEquiv n R S x.val,
    (mem_ofMatrixSubgroups_affinePoints_iff R S x.val).mp x.property⟩
  invFun g := ⟨(affinePointsEquiv n R S).symm g.val,
    (mem_ofMatrixSubgroups_affinePoints_iff R S _).mpr
      (by simpa only [MulEquiv.apply_symm_apply] using g.property)⟩
  left_inv x := Subtype.ext ((affinePointsEquiv n R S).symm_apply_apply x.val)
  right_inv g := Subtype.ext ((affinePointsEquiv n R S).apply_symm_apply g.val)
  map_mul' x y := Subtype.ext ((affinePointsEquiv n R S).map_mul x.val y.val)

@[simp] theorem ofMatrixSubgroupsAffineEquiv_coe {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    (S : CommAlgCat.{u} R)
    (x : (ofMatrixSubgroups (R := R) H hH).carrier ((algSpec R).obj (op S))) :
    (ofMatrixSubgroupsAffineEquiv R S x : GL n S) = affinePointsEquiv n R S x.val :=
  rfl

@[simp] theorem ofMatrixSubgroupsAffineEquiv_symm_coe
    {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    (S : CommAlgCat.{u} R) (g : H (CommRingCat.of S)) :
    ((ofMatrixSubgroupsAffineEquiv (hH := hH) R S).symm g).val =
      (affinePointsEquiv n R S).symm g.val :=
  rfl

variable (n) (e w : n → ℤ)

/-- The subgroup functor of points that are block unipotent for `e` and block diagonal
for `w`. -/
def leviUnipotent : SubgroupFunctor (groupScheme n R) :=
  ofMatrixSubgroups (fun A => blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w)
    (fun f _ hg => ⟨map_mem_blockUnipotentSubgroup e f.hom hg.1,
      map_mem_blockLeviSubgroup w f.hom hg.2⟩)

variable {n}

theorem mem_leviUnipotent {T : Over (Spec R)} {x : T ⟶ (groupScheme n R).X} :
    x ∈ (leviUnipotent n R e w).carrier T ↔
      x ∈ (blockUnipotent n R e).carrier T ∧ x ∈ (blockLevi n R w).carrier T :=
  Iff.rfl

theorem leviUnipotent_le : leviUnipotent n R e w ≤ blockUnipotent n R e :=
  fun _ _ hx => hx.1

/-- Affine points of the block unipotent subgroup functor are the block unipotent matrices. -/
def blockUnipotentAffineEquiv (S : CommAlgCat.{u} R) :
    (blockUnipotent n R e).carrier ((algSpec R).obj (op S)) ≃* blockUnipotentSubgroup S e :=
  ofMatrixSubgroupsAffineEquiv (H := fun A => blockUnipotentSubgroup A e)
    (hH := fun f _ hg => map_mem_blockUnipotentSubgroup e f.hom hg) R S

/-- Affine points of `leviUnipotent` are the matrices that are block unipotent for `e` and
block diagonal for `w`. -/
def leviUnipotentAffineEquiv (S : CommAlgCat.{u} R) :
    (leviUnipotent n R e w).carrier ((algSpec R).obj (op S)) ≃*
      ↥(blockUnipotentSubgroup S e ⊓ blockLeviSubgroup S w) :=
  ofMatrixSubgroupsAffineEquiv
    (H := fun A => blockUnipotentSubgroup A e ⊓ blockLeviSubgroup A w)
    (hH := fun f _ hg => ⟨map_mem_blockUnipotentSubgroup e f.hom hg.1,
      map_mem_blockLeviSubgroup w f.hom hg.2⟩) R S

variable {e w} (hw : ∀ i j, e i ≤ e j → w i ≤ w j)

include hw in
theorem blockUnipotent_le_of_le : blockUnipotent n R w ≤ blockUnipotent n R e :=
  fun _ _ hx => blockUnipotentSubgroup_le_of_le hw hx

/-- The coarser block Levi projection on affine points of the finer block unipotent subgroup
functor. -/
def pointsLeviProjection (S : CommAlgCat.{u} R) :
    (blockUnipotent n R e).carrier ((algSpec R).obj (op S)) →*
      (leviUnipotent n R e w).carrier ((algSpec R).obj (op S)) :=
  (leviUnipotentAffineEquiv R e w S).symm.toMonoidHom.comp
    ((unipotentLeviProjection S hw).comp
      (blockUnipotentAffineEquiv R e S).toMonoidHom)

theorem affinePointsEquiv_pointsLeviProjection (S : CommAlgCat.{u} R)
    (x : (blockUnipotent n R e).carrier ((algSpec R).obj (op S))) :
    affinePointsEquiv n R S (pointsLeviProjection R hw S x).val =
      unipotentLeviProjection S hw (blockUnipotentAffineEquiv R e S x) :=
  (affinePointsEquiv n R S).apply_symm_apply _

/-- The projection splits the inclusion of the Levi part. -/
theorem pointsLeviProjection_inclusion (S : CommAlgCat.{u} R)
    (m : (leviUnipotent n R e w).carrier ((algSpec R).obj (op S))) :
    pointsLeviProjection R hw S
        (Subgroup.inclusion (leviUnipotent_le R e w _) m) = m := by
  apply Subtype.ext
  apply (affinePointsEquiv n R S).injective
  rw [affinePointsEquiv_pointsLeviProjection]
  exact unipotentLeviProjection_of_mem hw _ (leviUnipotentAffineEquiv R e w S m).property

/-- The kernel of the projection is the coarser block unipotent subgroup functor. -/
theorem pointsLeviProjection_eq_one_iff (S : CommAlgCat.{u} R)
    (x : (blockUnipotent n R e).carrier ((algSpec R).obj (op S))) :
    pointsLeviProjection R hw S x = 1 ↔
      x.val ∈ (blockUnipotent n R w).carrier ((algSpec R).obj (op S)) := by
  have hiff : x.val ∈ (blockUnipotent n R w).carrier ((algSpec R).obj (op S)) ↔
      affinePointsEquiv n R S x.val ∈ blockUnipotentSubgroup S w :=
    mem_ofMatrixSubgroups_affinePoints_iff (H := fun A => blockUnipotentSubgroup A w)
      (hH := fun f _ hg => map_mem_blockUnipotentSubgroup w f.hom hg) R S x.val
  refine Iff.trans ?_
    ((unipotentLeviProjection_eq_one_iff hw (blockUnipotentAffineEquiv R e S x)).trans hiff.symm)
  change (leviUnipotentAffineEquiv R e w S).symm _ = 1 ↔ _
  rw [MulEquiv.symm_apply_eq, map_one]
  exact Iff.rfl

/-- The projection commutes with coefficient extension along an algebra map. -/
theorem pointsLeviProjection_naturality {S S' : CommAlgCat.{u} R} (g : S ⟶ S')
    (x : (blockUnipotent n R e).carrier ((algSpec R).obj (op S))) :
    (algSpec R).map g.op ≫ (pointsLeviProjection R hw S x).val =
      (pointsLeviProjection R hw S'
        ⟨(algSpec R).map g.op ≫ x.val, (blockUnipotent n R e).comp_mem _ x.property⟩).val := by
  apply (affinePointsEquiv n R S').injective
  have hx : blockUnipotentAffineEquiv R e S'
      ⟨(algSpec R).map g.op ≫ x.val, (blockUnipotent n R e).comp_mem _ x.property⟩ =
      ⟨Matrix.GeneralLinearGroup.map g.hom.toRingHom (blockUnipotentAffineEquiv R e S x).val,
        map_mem_blockUnipotentSubgroup e _ (blockUnipotentAffineEquiv R e S x).property⟩ :=
    Subtype.ext (affinePointsEquiv_naturality g x.val)
  rw [affinePointsEquiv_naturality, affinePointsEquiv_pointsLeviProjection,
    affinePointsEquiv_pointsLeviProjection, hx]
  exact map_unipotentLeviProjection hw g.hom.toRingHom _

/-- For topological coefficients, the projection is continuous on affine points. -/
theorem continuous_pointsLeviProjection (S : CommAlgCat.{u} R) [TopologicalSpace S]
    [IsTopologicalRing S] : Continuous (pointsLeviProjection R hw S) := by
  refine continuous_induced_rng.mpr ?_
  change Continuous fun x => (affinePointsEquiv n R S).symm
    (unipotentLeviProjection S hw (blockUnipotentAffineEquiv R e S x) : GL n S)
  refine (continuous_affinePointsEquiv_symm n R S).comp (continuous_subtype_val.comp
    ((continuous_unipotentLeviProjection hw).comp ?_))
  exact ((continuous_affinePointsEquiv n R S).comp continuous_subtype_val).subtype_mk _

end Points

end Langlands.GroupScheme.GeneralLinear
