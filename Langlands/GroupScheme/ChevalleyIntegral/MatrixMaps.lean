import Langlands.GroupScheme.SplitExistence.SchemeGroup

/-! # Chevalley torus and root maps over a commutative ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  (R : CommRingCat.{u})

/-- The ambient general linear group over the chosen ring. -/
abbrev GLR : GroupScheme (Spec R) := GeneralLinear.groupScheme (Fin D.n) R

/-- The diagonalizable group of the full character lattice over the chosen ring. -/
abbrev TR : CommGroupScheme (Spec R) := Diagonalizable.groupScheme R X

/-- Characters of the full lattice describe torus points on every test scheme. -/
def torusPointsEquivOver (T : Over (Spec R)) :
    (T ⟶ (TR (X := X) R).toGrp.X) ≃* (Multiplicative X →* (Γ(T.left, ⊤))ˣ) :=
  Corepresented.pointsEquiv (Diagonalizable.functor R X)
    (Diagonalizable.grpCorepresentation R X) T

/-- The natural diagonal matrix representation on affine algebras. -/
def torusTransformation : Diagonalizable.functor R X ⟶ GeneralLinear.functor (Fin D.n) R where
  app A := GrpCat.ofHom (D.torusHom (K := A))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    exact (D.torusHom_map f.hom.toRingHom χ).symm

/-- The full-lattice torus homomorphism over an arbitrary commutative ring. -/
def torusToGLOver : (TR (X := X) R).toGrp ⟶ D.GLR R :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation R X)
    (GeneralLinear.corepresentableBy (Fin D.n) R) (D.torusTransformation R)

theorem pointsEquiv_torusToGLOver (T : Over (Spec R))
    (x : T ⟶ (TR (X := X) R).toGrp.X) :
    GeneralLinear.pointsEquiv (Fin D.n) R T (x ≫ (D.torusToGLOver R).hom.hom) =
      D.torusHom (torusPointsEquivOver R T x) :=
  Corepresented.groupSchemeMap_points _ _ _ x

instance mono_torusToGLOver : Mono (D.torusToGLOver R).hom.hom := by
  constructor
  intro T x y h
  apply (torusPointsEquivOver R T).injective
  apply D.torusHom_injective
  rw [← pointsEquiv_torusToGLOver, ← pointsEquiv_torusToGLOver, h]

/-- The coordinate algebra map of the integral torus representation. -/
def torusClassify :
    GeneralLinear.CoordinateRing (Fin D.n) R →ₐ[R] AddMonoidAlgebra R X :=
  GeneralLinear.classify (D.torusHom (Diagonalizable.monomialUnits R X))

theorem torusClassify_entry (c : Fin D.n) :
    D.torusClassify R
      (GeneralLinear.quotient (Fin D.n) R
        (MvPolynomial.X (GeneralLinear.Coordinate.entry c c))) =
      AddMonoidAlgebra.single (D.wt c) 1 := by
  rw [torusClassify, GeneralLinear.classify_entry, coe_torusHom, diagonal_apply_eq]
  rfl

theorem torusClassify_inverseEntry (c : Fin D.n) :
    D.torusClassify R
      (GeneralLinear.quotient (Fin D.n) R
        (MvPolynomial.X (GeneralLinear.Coordinate.inverseEntry c c))) =
      AddMonoidAlgebra.single (-D.wt c) 1 := by
  rw [torusClassify, GeneralLinear.classify_inverseEntry]
  change (diagonal fun c =>
    (((Diagonalizable.monomialUnits R X (.ofAdd (D.wt c)))⁻¹ :
      (AddMonoidAlgebra R X)ˣ) : AddMonoidAlgebra R X)) c c = _
  rw [diagonal_apply_eq, ← map_inv]
  rfl

/-- Full-lattice generation by the representation weights makes the coordinate map
surjective over every commutative ring, including the zero ring. -/
theorem torusClassify_surjective : Function.Surjective (D.torusClassify R) := by
  let φ := D.torusClassify R
  have hw (c : Fin D.n) :
      AddMonoidAlgebra.single (D.wt c) (1 : R) ∈ φ.range ∧
        AddMonoidAlgebra.single (-D.wt c) (1 : R) ∈ φ.range :=
    ⟨⟨_, D.torusClassify_entry R c⟩, ⟨_, D.torusClassify_inverseEntry R c⟩⟩
  have hmon (x : X) :
      AddMonoidAlgebra.single x (1 : R) ∈ φ.range ∧
        AddMonoidAlgebra.single (-x) (1 : R) ∈ φ.range := by
    have hx : x ∈ AddSubgroup.closure (Set.range D.wt) := by
      rw [D.closure_range_wt]
      trivial
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact hw c
    | zero => simpa only [neg_zero, ← AddMonoidAlgebra.one_def] using
        And.intro φ.range.one_mem φ.range.one_mem
    | add x y _ _ hx hy =>
      constructor
      · simpa only [AddMonoidAlgebra.single_mul_single, one_mul] using
          φ.range.mul_mem hx.1 hy.1
      · simpa only [AddMonoidAlgebra.single_mul_single, one_mul, neg_add] using
          φ.range.mul_mem hx.2 hy.2
    | neg x _ hx => simpa only [neg_neg] using And.intro hx.2 hx.1
  apply (AlgHom.range_eq_top φ).1
  apply Algebra.eq_top_iff.2
  intro z
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact φ.range.zero_mem
  | add z w hz hw => exact φ.range.add_mem hz hw
  | single x r =>
    simpa only [AddMonoidAlgebra.smul_single', smul_eq_mul, mul_one] using
      φ.range.smul_mem (hmon x).1 r

/-- The underlying torus morphism is the spectrum of the explicit coordinate map. -/
theorem torusToGLOver_hom_left :
    (D.torusToGLOver R).hom.hom.left =
      Spec.map (CommRingCat.ofHom (D.torusClassify R).toRingHom) := by
  rw [torusToGLOver, Corepresented.groupSchemeMap_hom]
  rfl

/-- The full-lattice torus is a closed subgroup of the ambient matrix group over every
commutative ring. -/
theorem isClosedSubgroup_torusToGLOver : IsClosedSubgroup (D.torusToGLOver R) := by
  change IsClosedImmersion (D.torusToGLOver R).hom.hom.left
  rw [torusToGLOver_hom_left]
  exact IsClosedImmersion.spec_of_surjective _ (D.torusClassify_surjective R)

/-- The additive group over the chosen ring. -/
abbrev GaR : GroupScheme (Spec R) := VectorGroup.groupScheme R 1

/-- The scalar coordinate on points of the additive group. -/
def gaCoordOver (T : Over (Spec R)) : (T ⟶ (GaR R).X) →* Multiplicative Γ(T.left, ⊤) :=
  (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 1 => Γ(T.left, ⊤)) 0)).comp
    (VectorGroup.coordinates R 1 T).toMonoidHom

/-- The root exponential on points over every test scheme. -/
def rootPointsHomOver (j : J) (T : Over (Spec R)) :
    (T ⟶ (GaR R).X) →* (T ⟶ (D.GLR R).X) :=
  (GeneralLinear.pointsEquiv (Fin D.n) R T).symm.toMonoidHom.comp
    ((D.rootHom (K := Γ(T.left, ⊤)) j).comp (gaCoordOver R T))

theorem rootPointsHomOver_naturality (j : J) {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (GaR R).X) :
    D.rootPointsHomOver R j T' (a ≫ x) = a ≫ D.rootPointsHomOver R j T x := by
  apply (GeneralLinear.pointsEquiv (Fin D.n) R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [rootPointsHomOver, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  change D.x j (Multiplicative.toAdd (gaCoordOver R T' (a ≫ x))) =
    Matrix.GeneralLinearGroup.map _ (D.x j (Multiplicative.toAdd (gaCoordOver R T x)))
  rw [D.x_map]
  congr 1

/-- The root homomorphism from the additive group to the ambient matrix group. -/
def rootToGLOver (j : J) : GaR R ⟶ D.GLR R :=
  homOfPoints (D.rootPointsHomOver R j) fun a x => D.rootPointsHomOver_naturality R j a x

theorem pointsEquiv_rootToGLOver (j : J) (T : Over (Spec R))
    (x : T ⟶ (GaR R).X) :
    GeneralLinear.pointsEquiv (Fin D.n) R T (x ≫ (D.rootToGLOver R j).hom.hom) =
      D.x j (Multiplicative.toAdd (gaCoordOver R T x)) := by
  rw [rootToGLOver, comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

variable (k : Type u) [Field k]

/-- Over a field the ring-level torus map is the existing Chevalley torus map. -/
theorem torusToGLOver_eq :
    D.torusToGLOver (CommRingCat.of k) = D.torusToGL k := by
  apply Grp.hom_ext
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) _).injective
  simpa only [Category.id_comp] using
    (D.pointsEquiv_torusToGLOver (CommRingCat.of k) _ (𝟙 _)).trans
      (D.pointsEquiv_torusToGL k _ (𝟙 _)).symm

/-- Over a field the ring-level root map is the existing Chevalley root map. -/
theorem rootToGLOver_eq (j : J) :
    D.rootToGLOver (CommRingCat.of k) j = D.rootToGL k j := rfl

end Langlands.GroupScheme.SplitExistence.ChevalleyData
