import Langlands.GroupScheme.IntegralModel.GreenbergMixed.Represent
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.IntegralModel

/-! # Greenberg group schemes from a Greenberg ring scheme

For a Greenberg ring scheme `ℛ` of level `n` and a smooth affine group scheme `X` over `R`,
the group functor `B ↦ X(ℛ(B))` on `k`-algebras is corepresented by a smooth finitely
presented `k`-algebra. Its spectrum is a smooth affine `k`-group whose `k`-points are
`X(R ⧸ 𝔪ⁿ)`, functorially in `X`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.GreenbergMixed

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ+} (ℛ : GreenbergRingScheme R n)

local notation "κ" => CommRingCat.of (IsLocalRing.ResidueField R)

section Coordinates

variable (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom]

/-- The chosen coordinate algebra of `X` corepresents its algebra points. -/
abbrev coordCorep :
    (X.affinePointFunctor ⋙ forget GrpCat).CorepresentableBy (Lie.coordinateAlgebra X) :=
  AffineLinearEmbedding.corepresentableBy X (Lie.coordinateIso X)

omit [IsLocalRing R] in
/-- The coordinate algebra of a smooth affine group scheme is smooth. -/
theorem smooth_coordinateAlgebra (hX : Smooth X.X.hom) :
    Algebra.Smooth R (Lie.coordinateAlgebra X) := by
  have : IsIso (Lie.coordinateIso X).hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso (Lie.coordinateIso X)).hom)
  have h : Smooth ((algSpec (CommRingCat.of R)).obj (op (Lie.coordinateAlgebra X))).hom := by
    rw [← Over.w (Lie.coordinateIso X).hom]
    infer_instance
  exact (Corepresented.smooth_groupScheme_iff (e := coordCorep X)).1 h

/-- A surjection from a polynomial algebra in finitely many variables onto the coordinate
algebra of `X`. -/
structure CoordPres where
  /-- The number of variables. -/
  N : ℕ
  /-- The surjection. -/
  f : MvPolynomial (Fin N) R →ₐ[R] Lie.coordinateAlgebra X
  surj : Function.Surjective f

omit [IsLocalRing R] in
theorem nonempty_coordPres (hX : Smooth X.X.hom) : Nonempty (CoordPres X) := by
  have := smooth_coordinateAlgebra X hX
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType R (Lie.coordinateAlgebra X))
  exact ⟨⟨N, f, hf⟩⟩

end Coordinates

section Group

variable (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom]

/-- The Greenberg point functor `B ↦ X(ℛ(B))`. -/
abbrev pointFunctor : CommAlgCat.{u} κ ⥤ GrpCat.{u} := ℛ.functor ⋙ X.affinePointFunctor

/-- The representing algebra corepresents the Greenberg point functor. -/
def corep (P : CoordPres X) :
    (pointFunctor ℛ X ⋙ forget GrpCat).CorepresentableBy (ℛ.repAlg P.f) :=
  ℛ.corepresentableBy P.surj (coordCorep X)

/-- **The Greenberg group scheme** of `X` at level `n`. -/
abbrev greenbergGroup (P : CoordPres X) : GroupScheme (Spec κ) :=
  Corepresented.groupScheme (pointFunctor ℛ X) (corep ℛ X P)

instance isAffineHom_greenbergGroup (P : CoordPres X) :
    IsAffineHom (greenbergGroup ℛ X P).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

theorem smooth_greenbergGroup (P : CoordPres X) (hX : Smooth X.X.hom) :
    Smooth (greenbergGroup ℛ X P).X.hom := by
  rw [Corepresented.smooth_groupScheme_iff]
  have := smooth_coordinateAlgebra X hX
  exact { formallySmooth := ℛ.formallySmooth_repAlg P.surj
          finitePresentation := ℛ.finitePresentation_repAlg (f := P.f) }

end Group

section Points

/-- Precomposition with an isomorphism of test objects, as a group isomorphism of points. -/
def precomp {S : Scheme.{u}} (G : GroupScheme S) {T T' : Over S} (i : T ≅ T') :
    (T' ⟶ G.X) ≃* (T ⟶ G.X) :=
  (G.points.mapIso i.op).groupIsoToMulEquiv

theorem precomp_apply {S : Scheme.{u}} (G : GroupScheme S) {T T' : Over S} (i : T ≅ T')
    (x : T' ⟶ G.X) : precomp G i x = i.hom ≫ x := rfl

/-- The base point `Spec A` over itself is the affine test of `A`. -/
def baseTestIso (A : Type u) [CommRing A] :
    Over.mk (𝟙 (Spec (CommRingCat.of A))) ≅
      (algSpec (CommRingCat.of A)).obj (op (CommAlgCat.of (CommRingCat.of A) A)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (𝟙 (CommRingCat.of A)) = 𝟙 _
    rw [Spec.map_id, Category.comp_id])

/-- The congruence base is the affine test of `R ⧸ 𝔪ⁿ`. -/
def congruenceTestIso :
    Over.mk (congruenceBaseMap R n) ≅
      (algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of (CommRingCat.of R) (congruenceRing R n))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (congruenceRing R n))) =
      Spec.map (CommRingCat.ofHom (congruenceQuotient R n))
    rw [Category.id_comp]
    rfl)

/-- The level isomorphism `R ⧸ 𝔪ⁿ ≅ ℛ(k)` in `CommAlgCat R`. -/
def levelIso : CommAlgCat.of (CommRingCat.of R) (congruenceRing R n) ≅
    ℛ.functor.obj (CommAlgCat.of κ (IsLocalRing.ResidueField R)) :=
  CommAlgCat.isoMk ℛ.levelEquiv.symm

variable (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom] (P : CoordPres X)

variable {Z : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom Z.X.hom] (Q : CoordPres Z)

/-- The corepresentation as a group isomorphism `X(ℛ(S)) ≃* G_X(S)`. -/
def greenbergPointsEquiv (S : CommAlgCat.{u} κ) :
    ((algSpec (CommRingCat.of R)).obj (op (ℛ.functor.obj S)) ⟶ X.X) ≃*
      ((algSpec κ).obj (op S) ⟶ (greenbergGroup ℛ X P).X) :=
  (Corepresented.affinePointsEquiv (pointFunctor ℛ X) (corep ℛ X P) S).symm

/-- **Greenberg points.** The level-`n` points of `X` are the `k`-points of its Greenberg
group. -/
def levelPointsEquiv :
    rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj X) ≃*
      rationalPoints (greenbergGroup ℛ X P) :=
  ((((baseChangeBasePointsEquiv (congruenceBaseMap R n) X).trans
    (precomp X (congruenceTestIso (R := R) (n := n)).symm)).trans
    (precomp X ((algSpec (CommRingCat.of R)).mapIso (levelIso ℛ).op))).trans
    (greenbergPointsEquiv ℛ X P (CommAlgCat.of κ (IsLocalRing.ResidueField R)))).trans
    (precomp (greenbergGroup ℛ X P) (baseTestIso (IsLocalRing.ResidueField R)))

/-- The natural transformation of Greenberg point functors induced by a homomorphism. -/
abbrev pointNatTrans (h : Z ⟶ X) : pointFunctor ℛ Z ⟶ pointFunctor ℛ X :=
  Functor.whiskerLeft ℛ.functor (Functor.whiskerLeft (algSpec (CommRingCat.of R)).rightOp
    (pointsMap h))

/-- **The Greenberg homomorphism** induced by a homomorphism of group schemes. -/
def greenbergMap (h : Z ⟶ X) : greenbergGroup ℛ Z Q ⟶ greenbergGroup ℛ X P :=
  Corepresented.groupSchemeMap (corep ℛ Z Q) (corep ℛ X P) (pointNatTrans ℛ X h)

theorem affinePointsEquiv_symm_comp (h : Z ⟶ X) (S : CommAlgCat.{u} κ)
    (y : (pointFunctor ℛ Z).obj S) :
    (Corepresented.affinePointsEquiv (pointFunctor ℛ X) (corep ℛ X P) S).symm
        (y ≫ h.hom.hom) =
      (Corepresented.affinePointsEquiv (pointFunctor ℛ Z) (corep ℛ Z Q) S).symm y ≫
        (greenbergMap ℛ X P Q h).hom.hom := by
  apply (Corepresented.affinePointsEquiv (pointFunctor ℛ X) (corep ℛ X P) S).injective
  rw [MulEquiv.apply_symm_apply, greenbergMap, Corepresented.groupSchemeMap_affinePoints,
    MulEquiv.apply_symm_apply]
  rfl

theorem greenbergPointsEquiv_comp (h : Z ⟶ X) (S : CommAlgCat.{u} κ)
    (y : (algSpec (CommRingCat.of R)).obj (op (ℛ.functor.obj S)) ⟶ Z.X) :
    greenbergPointsEquiv ℛ X P S (y ≫ h.hom.hom) =
      greenbergPointsEquiv ℛ Z Q S y ≫ (greenbergMap ℛ X P Q h).hom.hom :=
  affinePointsEquiv_symm_comp ℛ X P Q h S y

/-- The Greenberg points equivalence is natural in the group scheme. -/
theorem levelPointsEquiv_naturality (h : Z ⟶ X)
    (z : rationalPoints ((GroupScheme.baseChange (congruenceBaseMap R n)).obj Z)) :
    levelPointsEquiv ℛ X P
        (rationalPoints.map ((GroupScheme.baseChange (congruenceBaseMap R n)).map h) z) =
      rationalPoints.map (greenbergMap ℛ X P Q h) (levelPointsEquiv ℛ Z Q z) := by
  simp only [levelPointsEquiv, MulEquiv.trans_apply, precomp_apply, rationalPoints.map_apply]
  rw [baseChangeBasePointsEquiv_comp, ← Category.assoc _ _ h.hom.hom,
    ← Category.assoc _ _ h.hom.hom, greenbergPointsEquiv_comp ℛ X P Q h, Category.assoc]

end Points

end Langlands.GroupScheme.IntegralModel.GreenbergMixed
