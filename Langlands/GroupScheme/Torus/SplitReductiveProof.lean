import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Torus.SplitReductiveStatement

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-! ### Transport along isomorphisms over the base -/

/-- Affineness of the structure morphism is preserved by an isomorphism over the base. -/
theorem isAffineHom_of_over_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    (hY : IsAffineHom Y.hom) : IsAffineHom X.hom := by
  let : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- Connectedness of the total space is preserved by an isomorphism over the base. -/
theorem connectedSpace_of_over_iso {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    (hY : ConnectedSpace Y.left) : ConnectedSpace X.left :=
  (Scheme.homeoOfIso ((Over.forget S).mapIso e)).connectedSpace_iff.2 hY

namespace splitTorus

variable (I : Type u) (R : CommRingCat.{u})

/-! ### The Laurent polynomial model -/

/-- The Laurent polynomial algebra `R[t_i^{± 1} : i ∈ I]`, as the group algebra of `ℤ^(I)`. -/
abbrev LaurentAlgebra : Type u := AddMonoidAlgebra R (I →₀ ℤ)

/-- The coordinate unit `t_i`. -/
def coordUnit (i : I) : (LaurentAlgebra I R)ˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (Finsupp.single i (-1)) 1
  val_inv := by
    rw [AddMonoidAlgebra.single_mul_single, ← Finsupp.single_add]
    simp [AddMonoidAlgebra.one_def]
  inv_val := by
    rw [AddMonoidAlgebra.single_mul_single, ← Finsupp.single_add]
    simp [AddMonoidAlgebra.one_def]

/-- The functor `A ↦ (I → Aˣ)` on commutative `R`-algebras. -/
def unitsFunctor : CommAlgCat.{u} R ⥤ GrpCat.{u} where
  obj A := GrpCat.of (I → Aˣ)
  map f := GrpCat.ofHom ((Units.map f.hom.toRingHom.toMonoidHom).compLeft I)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `R`-algebra maps out of the Laurent algebra are families of units indexed by `I`. -/
def algHomEquiv (A : Type u) [CommRing A] [Algebra R A] :
    (LaurentAlgebra I R →ₐ[R] A) ≃ (I → Aˣ) :=
  (AddMonoidAlgebra.lift R A (I →₀ ℤ)).symm.trans <|
    MonoidHom.toHomUnitsMulEquiv.toEquiv.trans <|
      AddMonoidHom.toMultiplicativeLeft.symm.trans <|
        Finsupp.liftAddHom.toEquiv.symm.trans <|
          Equiv.piCongrRight fun _ => (zmultiplesHom (Additive Aˣ)).symm.trans Additive.toMul

theorem algHomEquiv_apply_val (A : Type u) [CommRing A] [Algebra R A]
    (φ : LaurentAlgebra I R →ₐ[R] A) (i : I) :
    (algHomEquiv I R A φ i : A) = φ (AddMonoidAlgebra.single (Finsupp.single i 1) 1) :=
  rfl

/-- The Laurent algebra corepresents the functor of families of units. -/
def corepresentableBy :
    (unitsFunctor I R ⋙ forget GrpCat).CorepresentableBy
      (CommAlgCat.of R (LaurentAlgebra I R)) where
  homEquiv {A} := (ConcreteCategory.homEquiv (C := CommAlgCat.{u} R)).trans (algHomEquiv I R A)
  homEquiv_comp {A A'} g f := by
    funext i
    apply Units.ext
    rfl

/-- The split torus over `Spec R` built as `Spec` of the Laurent algebra. -/
abbrev laurentGroupScheme : GroupScheme (Spec R) :=
  Corepresented.groupScheme (unitsFunctor I R) (corepresentableBy I R)

/-- Points of the Laurent model are families of global units. -/
def laurentPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (laurentGroupScheme I R).X) ≃* (I → (Γ(T.left, ⊤))ˣ) :=
  Corepresented.pointsEquiv (unitsFunctor I R) (corepresentableBy I R) T

theorem laurentPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (laurentGroupScheme I R).X) :
    laurentPointsEquiv I R T' (a ≫ x) = unitsRestrict I a (laurentPointsEquiv I R T x) := by
  exact Corepresented.pointsEquiv_naturality (unitsFunctor I R) (corepresentableBy I R) a x

/-- The split torus over `Spec R` is `Spec` of the Laurent algebra. -/
def laurentIso [Finite I] : splitTorus (Spec R) I ≅ laurentGroupScheme I R :=
  isoOfPointModels (fun T : Over (Spec R) => I → (Γ(T.left, ⊤))ˣ)
    (fun a => unitsRestrict I a) (pointsEquiv I) (laurentPointsEquiv I R)
    (fun a x => pointsEquiv_naturality I a x)
    (fun a y => laurentPointsEquiv_naturality I R a y)

theorem isAffineHom_laurentGroupScheme : IsAffineHom (laurentGroupScheme I R).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap R (LaurentAlgebra I R))))
  infer_instance

theorem connectedSpace_laurentGroupScheme (k : Type u) [Field k] :
    ConnectedSpace (laurentGroupScheme I (CommRingCat.of k)).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (LaurentAlgebra I (CommRingCat.of k))))
  infer_instance

end splitTorus

/-! ### Affineness and connectedness of split tori -/

theorem isAffineHom_splitTorus_spec (R : CommRingCat.{u}) (I : Type u) [Finite I] :
    IsAffineHom (splitTorus (Spec R) I).X.hom :=
  isAffineHom_of_over_iso ((Grp.forget _).mapIso (splitTorus.laurentIso I R))
    (splitTorus.isAffineHom_laurentGroupScheme I R)

/-- Split tori are affine over an arbitrary base. -/
theorem isAffineHom_splitTorus (S : Scheme.{u}) (I : Type u) [Finite I] :
    IsAffineHom (splitTorus S I).X.hom := by
  refine isAffineHom_of_over_iso
    ((Grp.forget _).mapIso (splitTorus.baseChangeIso (Gm.toSpecZ S) I).symm) ?_
  have h := isAffineHom_splitTorus_spec (CommRingCat.of (ULift.{u} ℤ)) I
  change IsAffineHom (pullback.snd _ _)
  exact isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) h

theorem IsSplitTorus.isAffineHom {S : Scheme.{u}} {G : GroupScheme S} (hG : IsSplitTorus G) :
    IsAffineHom G.X.hom := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact isAffineHom_of_over_iso ((Grp.forget _).mapIso e) (isAffineHom_splitTorus S I)

theorem IsSplitTorus.connectedSpace {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitTorus G) :
    ConnectedSpace G.X.left := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact connectedSpace_of_over_iso ((Grp.forget _).mapIso (e ≪≫ splitTorus.laurentIso I _))
    (splitTorus.connectedSpace_laurentGroupScheme I k)

/-! ### The unipotent radical of a split torus -/

namespace splitTorus

variable {R : CommRingCat.{u}} {I : Type u} [Finite I] {H : GroupScheme (Spec R)}

/-- The `j`-th coordinate character of a homomorphism into a split torus, as a one-dimensional
matrix representation. -/
def coordinateRepresentation (f : H ⟶ splitTorus (Spec R) I) (j : I) :
    MatrixRepresentation H Unit :=
  f ≫ Pi.π (fun _ : I => (Gm (Spec R)).toGrp) j ≫
    GeneralLinear.diagonalCocharacter Unit R (fun _ => 1)

theorem pointMatrix_coordinateRepresentation (f : H ⟶ splitTorus (Spec R) I) (j : I)
    (T : Over (Spec R)) (y : T ⟶ H.X) :
    (coordinateRepresentation f j).pointMatrix T y =
      GeneralLinear.diagonalUnits Γ(T.left, ⊤) (fun _ : Unit => (1 : ℤ))
        (pointsEquiv I T (y ≫ f.hom.hom) j) := by
  rw [MatrixRepresentation.pointMatrix_apply, pointsEquiv_apply]
  have h : y ≫ (coordinateRepresentation f j).hom.hom =
      ((y ≫ f.hom.hom) ≫ (Pi.π (fun _ : I => (Gm (Spec R)).toGrp) j).hom.hom) ≫
        (GeneralLinear.diagonalCocharacter Unit R fun _ => 1).hom.hom := by
    simp only [coordinateRepresentation, Grp.comp_hom_hom, Category.assoc]
  rw [h, GeneralLinear.pointsEquiv_diagonalCocharacter]

end splitTorus

/-- A split torus over a field has trivial unipotent radical: a unipotent subgroup has trivial
image under every coordinate character. -/
theorem IsSplitTorus.hasTrivialUnipotentRadical {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitTorus G) :
    HasTrivialUnipotentRadical G := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  intro H i _ _ _ hU _
  ext T x
  constructor
  · rw [SubgroupFunctor.mem_range, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    rintro ⟨y, rfl⟩
    apply ((isoPointsEquiv e T).trans (splitTorus.pointsEquiv I T)).injective
    rw [map_one]
    funext j
    apply Units.ext
    obtain ⟨v, hv0, hv⟩ := hU Unit (splitTorus.coordinateRepresentation (i ≫ e.hom) j)
    have h := congrFun (hv T y) ()
    rw [splitTorus.pointMatrix_coordinateRepresentation, GeneralLinear.coe_diagonalUnits,
      Matrix.mulVec_diagonal] at h
    have hv1 : v () ≠ 0 := fun h0 => hv0 (funext fun u => by cases u; exact h0)
    have hu : IsUnit (scalarMap T (v ())) := (Ne.isUnit hv1).map (scalarMap T)
    have h' := hu.mul_eq_right.1 (by simpa using h)
    simpa [Category.assoc] using h'
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    subst hx
    exact Subgroup.one_mem ((SubgroupFunctor.range i).carrier T)

/-- A split torus over a field is pseudo-reductive. -/
theorem IsSplitTorus.isPseudoReductive {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitTorus G) : IsPseudoReductive G :=
  ⟨hG.smooth, hG.isAffineHom, hG.connectedSpace, hG.hasTrivialUnipotentRadical⟩

/-- A split torus over a field is a connected reductive group. -/
theorem IsSplitTorus.isConnectedReductive {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSplitTorus G) : IsConnectedReductive G :=
  ⟨hG.smooth, hG.isAffineHom, hG.connectedSpace,
    (hG.baseChange (toAlgebraicClosure k)).hasTrivialUnipotentRadical⟩

/-- A split torus over an arbitrary base is a reductive group scheme. -/
theorem IsSplitTorus.isReductive {S : Scheme.{u}} {G : GroupScheme S} (hG : IsSplitTorus G) :
    IsReductive G :=
  ⟨hG.smooth, hG.isAffineHom, fun s => (hG.baseChange (geometricPoint S s)).isPseudoReductive⟩

/-- Split tori are reductive, over every field and over every base scheme. -/
theorem IsSplitTorus.reductiveStatement : IsSplitTorus.ReductiveStatement.{u} :=
  ⟨fun _ _ _ hG => hG.isConnectedReductive, fun _ _ hG => hG.isReductive⟩

end Langlands.GroupScheme
