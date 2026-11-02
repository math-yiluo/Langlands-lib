import Langlands.Cohomology.DiagramHomology
import Langlands.Cohomology.DivisibleSystem.CompatibleHomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Complexes of inverse systems and the limit of the Hom complexes

An `ℓ`-divisible system `T` of cochain complexes in an abelian category `C` is an inverse
system `T.tower : ℕᵒᵖ ⥤ CochainComplex C ℤ`. This module regards it as a single cochain
complex `towerComplex T` in the abelian category `ℕᵒᵖ ⥤ C` of inverse systems in `C`: its
degree `p` term is the inverse system `m ↦ (T m)^p` and its differentials are those of the
complexes `T m`.

* `diagramComplex F` turns a diagram of complexes `F : J ⥤ HomologicalComplex V c` into a
  complex of diagrams; Mathlib's `HomologicalComplex.asFunctor` recovers `F`. Its cohomology
  is computed objectwise (`diagramComplexHomologyIso`, from the Library's
  `diagramHomologyIso`); for `towerComplex T` this is `towerComplexHomologyIso`.
* For complexes `K`, `L` in an `R`-linear category, the degree `n` cohomology of the Library's
  module-valued Hom complex `LinearHomComplex.complex R K L` is, as an abelian group, the
  degree `n` cohomology of Mathlib's `CochainComplex.HomComplex K L`, hence the group of
  morphisms `K ⟶ L⟦n⟧` in the homotopy category (`linearHomComplexHomologyAddEquiv`,
  `linearHomComplexHomologyHomotopyAddEquiv`).
* The module-valued Hom complex between `towerComplex T` and `towerComplex W` is isomorphic to
  the complex of compatible families of the Library's `CompatibleHomComplex`, hence to
  `homComplexLimit R T W`, the inverse limit of the Hom complexes `Hom^•(T m, W m)`
  (`towerHomComplexIso`, `towerHomComplexIsoLimit`); the limit projections correspond to the
  evaluations at the levels (`towerHomComplexIsoLimit_hom_π`).
* Consequently the degree `n` cohomology of `homComplexLimit R T W` is the group of morphisms
  `towerComplex T ⟶ (towerComplex W)⟦n⟧` in the homotopy category of cochain complexes in
  `ℕᵒᵖ ⥤ C` (`homComplexLimitHomologyAddEquiv`).
* `smoothTowerComplex` is `towerComplex` for systems of complexes of smooth representations.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u vJ uJ v' u'

section DiagramComplex

variable {J : Type uJ} [Category.{vJ} J] {V : Type u'} [Category.{v'} V] [HasZeroMorphisms V]
  {ι : Type*} {c : ComplexShape ι}

/-- The complex of diagrams of a diagram of complexes `F : J ⥤ HomologicalComplex V c`: its
degree `i` term is the diagram `j ↦ (F j)^i` and its differentials are the differentials of
the complexes `F j`. -/
def diagramComplex (F : J ⥤ HomologicalComplex V c) : HomologicalComplex (J ⥤ V) c where
  X i := F ⋙ HomologicalComplex.eval V c i
  d i j := Functor.whiskerLeft F (HomologicalComplex.dNatTrans V c i j)
  shape i j h := by
    ext t
    exact (F.obj t).shape i j h
  d_comp_d' i j k _ _ := by
    ext t
    exact (F.obj t).d_comp_d i j k

@[simp]
lemma diagramComplex_X_obj (F : J ⥤ HomologicalComplex V c) (i : ι) (t : J) :
    ((diagramComplex F).X i).obj t = (F.obj t).X i :=
  rfl

@[simp]
lemma diagramComplex_X_map (F : J ⥤ HomologicalComplex V c) (i : ι) {t t' : J} (a : t ⟶ t') :
    ((diagramComplex F).X i).map a = (F.map a).f i :=
  rfl

@[simp]
lemma diagramComplex_d_app (F : J ⥤ HomologicalComplex V c) (i j : ι) (t : J) :
    ((diagramComplex F).d i j).app t = (F.obj t).d i j :=
  rfl

/-- Mathlib's `asFunctor` recovers the diagram of complexes. -/
lemma asFunctor_diagramComplex (F : J ⥤ HomologicalComplex V c) :
    (diagramComplex F).asFunctor = F :=
  rfl

/-- The chain map of complexes of diagrams induced by a morphism of diagrams of complexes. -/
@[simps]
def diagramComplexMap {F G : J ⥤ HomologicalComplex V c} (α : F ⟶ G) :
    diagramComplex F ⟶ diagramComplex G where
  f i := Functor.whiskerRight α (HomologicalComplex.eval V c i)
  comm' i j _ := by
    ext t
    exact (α.app t).comm i j

end DiagramComplex

section DiagramComplexHomology

variable {J : Type uJ} [Category.{vJ} J] {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι}

/-- The cohomology of `diagramComplex F` in degree `q` is the diagram of the cohomology
objects of the complexes `F j`. This is the Library's `diagramHomologyIso` at
`diagramComplex F`. -/
def diagramComplexHomologyIso (F : J ⥤ HomologicalComplex C c) (q : ι) :
    F ⋙ HomologicalComplex.homologyFunctor C c q ≅ (diagramComplex F).homology q :=
  (diagramHomologyIso c q).app (diagramComplex F)

@[simp]
lemma diagramComplexHomologyIso_hom_app (F : J ⥤ HomologicalComplex C c) (q : ι) (j : J) :
    (diagramComplexHomologyIso F q).hom.app j =
      (((diagramComplex F).sc q).mapHomologyIso ((evaluation J C).obj j)).hom :=
  rfl

end DiagramComplexHomology

section LinearHomComplexHomology

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The short complex of abelian groups underlying the module-valued Hom complex in degree `n`
is the short complex of Mathlib's `CochainComplex.HomComplex K L` in degree `n`; all three
components are identities. -/
def linearHomComplexScIso (K L : CochainComplex C ℤ) (n : ℤ) :
    ((LinearHomComplex.complex R K L).sc n).map (forget₂ (ModuleCat.{v} R) AddCommGrpCat) ≅
      (CochainComplex.HomComplex K L).sc n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by ext; rfl) (by ext; rfl)

/-- The degree `n` cohomology of the module-valued Hom complex is, as an abelian group, the
degree `n` cohomology of Mathlib's `CochainComplex.HomComplex K L`. -/
def linearHomComplexHomologyAddEquiv (K L : CochainComplex C ℤ) (n : ℤ) :
    (LinearHomComplex.complex R K L).homology n ≃+ (CochainComplex.HomComplex K L).homology n :=
  ((((LinearHomComplex.complex R K L).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat)).symm ≪≫
    ShortComplex.homologyMapIso (linearHomComplexScIso R K L n)).addCommGroupIsoToAddEquiv

/-- The degree `n` cohomology of the module-valued Hom complex is the group of morphisms
`K ⟶ L⟦n⟧` in the homotopy category. -/
def linearHomComplexHomologyHomotopyAddEquiv (K L : CochainComplex C ℤ) (n : ℤ) :
    (LinearHomComplex.complex R K L).homology n ≃+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
  (linearHomComplexHomologyAddEquiv R K L n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv K L n).trans
      CochainComplex.HomComplex.CohomologyClass.homAddEquiv)

end LinearHomComplexHomology

namespace DivisibleSystem

section TowerComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- The cochain complex of inverse systems of an `ℓ`-divisible system `T` of cochain
complexes: degree `p` is the inverse system `m ↦ (T m)^p`, i.e. the tower of `T.degree p`. -/
abbrev towerComplex (T : DivisibleSystem (CochainComplex C ℤ) ℓ) :
    CochainComplex (ℕᵒᵖ ⥤ C) ℤ :=
  diagramComplex T.tower

lemma towerComplex_X (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (p : ℤ) :
    (towerComplex T).X p = (T.degree p).tower :=
  rfl

/-- The cohomology of `towerComplex T` in degree `q` is the inverse system
`m ↦ H^q(T m)`. -/
def towerComplexHomologyIso (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (q : ℤ) :
    T.tower ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ≅
      (towerComplex T).homology q :=
  diagramComplexHomologyIso T.tower q

end TowerComplex

section TowerHomComplex

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {ℓ : ℕ} (T W : DivisibleSystem (CochainComplex C ℤ) ℓ)

/-- The evaluation at level `m` of a cochain between the complexes of inverse systems. -/
def towerCochainEval {n : ℤ} (z : Cochain (towerComplex T) (towerComplex W) n) (m : ℕ) :
    Cochain (T.obj m) (W.obj m) n :=
  Cochain.mk fun p q hpq => (z.v p q hpq).app (op m)

@[simp]
lemma towerCochainEval_v {n : ℤ} (z : Cochain (towerComplex T) (towerComplex W) n) (m : ℕ)
    (p q : ℤ) (hpq : p + n = q) :
    (towerCochainEval T W z m).v p q hpq = (z.v p q hpq).app (op m) :=
  Cochain.mk_v _ _ _ _

variable {T W} in
/-- The levels of a cochain between the complexes of inverse systems form a compatible
family: naturality of its components is the compatibility with `cochainTransition`. -/
lemma towerCochainEval_mem {n : ℤ} (z : Cochain (towerComplex T) (towerComplex W) n) :
    (fun m => towerCochainEval T W z m) ∈ compatibleCochains R T W n := by
  intro m' m h
  ext p q hpq
  rw [cochainTransition_v, towerCochainEval_v, towerCochainEval_v]
  exact (homTransition_eq_iff (T.degree p) (W.degree q) h _ _).2
    ((z.v p q hpq).naturality (homOfLE h).op)

variable {R T W} in
/-- The morphism of inverse systems `m ↦ (z m).v p q` of the component `(p, q)` of a
compatible family `z`; naturality is the compatibility of `z`. -/
@[simps]
def compatibleCochainsComponent {n : ℤ} (z : compatibleCochains R T W n) (p q : ℤ)
    (hpq : p + n = q) : (towerComplex T).X p ⟶ (towerComplex W).X q where
  app m := (z.1 m.unop).v p q hpq
  naturality m m' φ := by
    have h : m'.unop ≤ m.unop := leOfHom φ.unop
    obtain rfl : φ = (homOfLE h).op := Subsingleton.elim _ _
    have hz := Cochain.congr_v (z.2 h) p q hpq
    rw [cochainTransition_v] at hz
    exact (homTransition_eq_iff (T.degree p) (W.degree q) h _ _).1 hz

/-- Cochains between the complexes of inverse systems are the compatible families of
cochains between the levels. -/
def towerCochainLinearEquiv (n : ℤ) :
    Cochain (towerComplex T) (towerComplex W) n ≃ₗ[R] compatibleCochains R T W n where
  toFun z := ⟨fun m => towerCochainEval T W z m, towerCochainEval_mem R z⟩
  invFun z := Cochain.mk fun p q hpq => compatibleCochainsComponent z p q hpq
  map_add' z z' := by
    apply Subtype.ext
    funext m
    ext p q hpq
    simp [Cochain.add_v]
    rfl
  map_smul' r z := by
    apply Subtype.ext
    funext m
    ext p q hpq
    simp [Cochain.smul_v]
    rfl
  left_inv z := by
    ext p q hpq m
    rfl
  right_inv z := by
    apply Subtype.ext
    funext m
    ext p q hpq
    simp

@[simp]
lemma towerCochainLinearEquiv_apply_coe {n : ℤ} (z : Cochain (towerComplex T) (towerComplex W) n)
    (m : ℕ) : (towerCochainLinearEquiv R T W n z).1 m = towerCochainEval T W z m :=
  rfl

/-- The evaluation at a level commutes with the differentials of the Hom complexes. -/
lemma δ_towerCochainEval (n n' : ℤ) (z : Cochain (towerComplex T) (towerComplex W) n)
    (m : ℕ) : δ n n' (towerCochainEval T W z m) = towerCochainEval T W (δ n n' z) m := by
  ext p q hpq
  simp only [δ, Cochain.mk_v, towerCochainEval_v, NatTrans.app_add, NatTrans.comp_app,
    diagramComplex_d_app, Units.smul_def, NatTrans.app_zsmul]
  rfl

/-- The module-valued Hom complex between the complexes of inverse systems is the complex of
compatible families. -/
def towerHomComplexIso :
    LinearHomComplex.complex R (towerComplex T) (towerComplex W) ≅
      compatibleHomComplex R T W :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (towerCochainLinearEquiv R T W n).toModuleIso)
    (by
      intro n n' _
      ext z
      apply Subtype.ext
      funext m
      exact (δ_towerCochainEval T W n n' z m).symm)

/-- The module-valued Hom complex between the complexes of inverse systems is the inverse limit
of the Hom complexes `Hom^•(T m, W m)`. -/
def towerHomComplexIsoLimit :
    LinearHomComplex.complex R (towerComplex T) (towerComplex W) ≅ homComplexLimit R T W :=
  towerHomComplexIso R T W ≪≫ compatibleHomComplexIsoLimit R T W

/-- The evaluation at level `m`, as a chain map from the module-valued Hom complex between the
complexes of inverse systems to the Hom complex `Hom^•(T m, W m)`. -/
def towerHomComplexEval (m : ℕ) :
    LinearHomComplex.complex R (towerComplex T) (towerComplex W) ⟶
      LinearHomComplex.complex R (T.obj m) (W.obj m) where
  f n := ModuleCat.ofHom
    { toFun := fun z => towerCochainEval T W z m
      map_add' := fun z z' =>
        congrArg (fun z => z.1 m) ((towerCochainLinearEquiv R T W n).map_add z z')
      map_smul' := fun r z =>
        congrArg (fun z => z.1 m) ((towerCochainLinearEquiv R T W n).map_smul r z) }
  comm' n n' _ := by
    ext z
    exact (δ_towerCochainEval T W n n' z m).symm

@[simp]
lemma towerHomComplexEval_f_apply (m : ℕ) (n : ℤ)
    (z : Cochain (towerComplex T) (towerComplex W) n) :
    (towerHomComplexEval R T W m).f n z = towerCochainEval T W z m :=
  rfl

/-- The projections of `towerHomComplexIsoLimit` are the evaluations at the levels. -/
@[reassoc (attr := simp)]
lemma towerHomComplexIsoLimit_hom_π (m : ℕ) :
    (towerHomComplexIsoLimit R T W).hom ≫ limit.π (homComplexSystem R T W) (op m) =
      towerHomComplexEval R T W m := by
  rw [towerHomComplexIsoLimit, Iso.trans_hom, Category.assoc,
    compatibleHomComplexIsoLimit_hom_π]
  ext n z
  rfl

/-- The degree `n` cohomology of the inverse limit `homComplexLimit R T W` of the Hom complexes
`Hom^•(T m, W m)` is the group of morphisms `towerComplex T ⟶ (towerComplex W)⟦n⟧` in the
homotopy category of cochain complexes of inverse systems in `C`. -/
def homComplexLimitHomologyAddEquiv (n : ℤ) :
    (homComplexLimit R T W).homology n ≃+
      ((HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (ComplexShape.up ℤ)).obj (towerComplex T) ⟶
        (HomotopyCategory.quotient (ℕᵒᵖ ⥤ C) (ComplexShape.up ℤ)).obj
          ((towerComplex W)⟦n⟧)) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) n).mapIso
      (towerHomComplexIsoLimit R T W)).symm.toLinearEquiv.toAddEquiv.trans
    (linearHomComplexHomologyHomotopyAddEquiv R (towerComplex T) (towerComplex W) n)

end TowerHomComplex

end DivisibleSystem

section Smooth

variable {R : Type u} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G] {ℓ : ℕ}

/-- The cochain complex of inverse systems of smooth representations of an `ℓ`-divisible
system of cochain complexes of smooth representations: degree `p` is the inverse system
`m ↦ (T m)^p` in `ℕᵒᵖ ⥤ SmoothRep R G`. -/
abbrev smoothTowerComplex (T : SmoothRepComplexDivisibleSystem.{v, u, w} R G ℓ) :
    CochainComplex (ℕᵒᵖ ⥤ SmoothRep.{u, v, w} R G) ℤ :=
  DivisibleSystem.towerComplex T

end Smooth

end Langlands.Cohomology
