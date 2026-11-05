import Langlands.GroupScheme.SplitExistence.Points
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.Geometry

/-! # The torus and the root groups as group-scheme homomorphisms into `GL_n`

Over a field `k`, the diagonalizable group `D(X)` (Library `Diagonalizable.groupScheme`) maps to
`GL_n` by `χ ↦ diag(χ(wt c))`, and the vector group `𝔾ₐ` maps to `GL_n` by the root exponential
`s ↦ x_j(s)`, on points over every test scheme. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

theorem torusHom_map {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (χ : Multiplicative X →* Aˣ) :
    Matrix.GeneralLinearGroup.map f (D.torusHom χ) =
      D.torusHom ((Units.map f.toMonoidHom).comp χ) := by
  ext c d
  simp only [Matrix.GeneralLinearGroup.map_apply, coe_torusHom, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem x_map {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (j : J) (s : A) :
    Matrix.GeneralLinearGroup.map f (D.x j s) = D.x j (f s) := by
  ext c d
  rw [Matrix.GeneralLinearGroup.map_apply, coe_x, coe_x, ← divExp_map]
  rfl

theorem torusHom_injective {K : Type u} [CommRing K] :
    Function.Injective (D.torusHom (K := K)) := by
  intro χ ψ h
  have hw : ∀ c, χ (Multiplicative.ofAdd (D.wt c)) = ψ (Multiplicative.ofAdd (D.wt c)) := by
    intro c
    ext
    have := congrArg (fun g : GL (Fin D.n) K => (g : Matrix (Fin D.n) (Fin D.n) K) c c) h
    simpa [coe_torusHom] using this
  have key : ∀ x ∈ AddSubgroup.closure (Set.range D.wt),
      χ (Multiplicative.ofAdd x) = ψ (Multiplicative.ofAdd x) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hw c
    | zero => simp
    | add x y _ _ hx hy => rw [ofAdd_add, map_mul, map_mul, hx, hy]
    | neg x _ hx => rw [ofAdd_neg, map_inv, map_inv, hx]
  ext m
  have hm : Multiplicative.toAdd m ∈ AddSubgroup.closure (Set.range D.wt) := by
    rw [D.closure_range_wt]
    trivial
  exact congrArg Units.val (key _ hm)

variable (k : Type u) [Field k]

/-- `GL_n` over `Spec k`. -/
abbrev GLk : GroupScheme (Spec (CommRingCat.of k)) :=
  GeneralLinear.groupScheme (Fin D.n) (CommRingCat.of k)

/-- The split torus `D(X)` over `Spec k`. -/
abbrev Tk : CommGroupScheme (Spec (CommRingCat.of k)) :=
  Diagonalizable.groupScheme (CommRingCat.of k) X

omit [AddCommGroup Y] in
/-- The weight lattice of a root datum is torsion-free: it embeds into the `ℤ`-dual of the
coweight lattice. -/
theorem isTorsionFree_weight [AddCommGroup Y] (P : RootDatum J X Y) : Module.IsTorsionFree ℤ X := by
  refine ⟨fun r hr x y hxy => ?_⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact not_isRegular_zero hr
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective
  ext z
  have h := congrArg (fun w => P.toLinearMap w z) hxy
  simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hr0 h

/-- `D(X)` is a split torus for the weight lattice `X` of a root datum of finite rank. -/
theorem isSplitTorus_Tk [Module.Finite ℤ X] (P : RootDatum J X Y) :
    IsSplitTorus (Tk (X := X) k).toGrp := by
  have := isTorsionFree_weight P
  let B := Module.Free.chooseBasis ℤ X
  exact Langlands.GroupScheme.Diagonalizable.isSplitTorus (CommRingCat.of k)
    B.equivFun.toAddEquiv

/-- The points of `D(X)` as characters. -/
def torusPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Tk (X := X) k).toGrp.X) ≃* (Multiplicative X →* (Γ(T.left, ⊤))ˣ) :=
  Corepresented.pointsEquiv (Diagonalizable.functor (CommRingCat.of k) X)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) X) T

/-- The torus homomorphism on points over a test scheme. -/
def torusPointsHom (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Tk (X := X) k).toGrp.X) →* (T ⟶ (D.GLk k).X) :=
  (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T).symm.toMonoidHom.comp
    ((D.torusHom (K := Γ(T.left, ⊤))).comp (torusPointsEquiv k T).toMonoidHom)

theorem torusPointsHom_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    D.torusPointsHom k T' (a ≫ x) = a ≫ D.torusPointsHom k T x := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [torusPointsHom, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  rw [D.torusHom_map]
  congr 1

/-- The torus homomorphism `D(X) → GL_n`, `χ ↦ diag(χ(wt c))`. -/
def torusToGL : (Tk (X := X) k).toGrp ⟶ D.GLk k :=
  homOfPoints (D.torusPointsHom k) fun a x => D.torusPointsHom_naturality k a x

theorem pointsEquiv_torusToGL (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T (x ≫ (D.torusToGL k).hom.hom) =
      D.torusHom (torusPointsEquiv k T x) := by
  rw [torusToGL, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

instance mono_torusToGL : Mono (D.torusToGL k).hom.hom := by
  constructor
  intro T x y h
  apply (torusPointsEquiv k T).injective
  apply D.torusHom_injective
  rw [← pointsEquiv_torusToGL, ← pointsEquiv_torusToGL, h]

/-- The torus homomorphism is a closed subgroup embedding, because the weights generate `X`. -/
theorem isClosedSubgroup_torusToGL (hT : IsSplitTorus (Tk (X := X) k).toGrp) :
    IsClosedSubgroup (D.torusToGL k) := by
  have : Smooth (Tk (X := X) k).toGrp.X.hom := hT.smooth
  have : ConnectedSpace (Tk (X := X) k).toGrp.X.left := hT.connectedSpace
  have : Smooth (D.GLk k).X.hom := Langlands.GroupScheme.GeneralLinear.smoothStatement (Fin D.n) _
  have : LocallyOfFiniteType (D.GLk k).X.hom := inferInstance
  have : IsAffineHom (D.GLk k).X.hom := GeneralLinear.isAffineHom_groupScheme _ _
  have : IsAffineHom (Tk (X := X) k).toGrp.X.hom := Langlands.GroupScheme.Diagonalizable.isAffineHom _ _
  exact HomImage.isClosedSubgroup_of_mono (D.torusToGL k)

/-- The additive group `𝔾ₐ` over `Spec k`. -/
abbrev Gak : GroupScheme (Spec (CommRingCat.of k)) :=
  VectorGroup.groupScheme (CommRingCat.of k) 1

/-- The coordinate of a point of `𝔾ₐ`. -/
def gaCoord (T : Over (Spec (CommRingCat.of k))) : (T ⟶ (Gak k).X) →* Multiplicative Γ(T.left, ⊤) :=
  (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 1 => Γ(T.left, ⊤)) 0)).comp
    (VectorGroup.coordinates (CommRingCat.of k) 1 T).toMonoidHom

/-- The root homomorphism on points. -/
def rootPointsHom (j : J) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Gak k).X) →* (T ⟶ (D.GLk k).X) :=
  (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T).symm.toMonoidHom.comp
    ((D.rootHom (K := Γ(T.left, ⊤)) j).comp (gaCoord k T))

theorem rootPointsHom_naturality (j : J) {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (Gak k).X) :
    D.rootPointsHom k j T' (a ≫ x) = a ≫ D.rootPointsHom k j T x := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [rootPointsHom, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  change D.x j (Multiplicative.toAdd (gaCoord k T' (a ≫ x))) =
    Matrix.GeneralLinearGroup.map _ (D.x j (Multiplicative.toAdd (gaCoord k T x)))
  rw [D.x_map]
  congr 1

/-- The root homomorphism `𝔾ₐ → GL_n`, `s ↦ x_j(s)`. -/
def rootToGL (j : J) : Gak k ⟶ D.GLk k :=
  homOfPoints (D.rootPointsHom k j) fun a x => D.rootPointsHom_naturality k j a x

theorem pointsEquiv_rootToGL (j : J) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gak k).X) :
    GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T (x ≫ (D.rootToGL k j).hom.hom) =
      D.x j (Multiplicative.toAdd (gaCoord k T x)) := by
  rw [rootToGL, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
