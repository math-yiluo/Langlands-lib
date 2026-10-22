import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Linear Hom complexes

Module-valued Hom complexes with contravariant and covariant chain maps.
Their terms and differential reuse Mathlib's actual graded cochains.
-/

noncomputable section

namespace Langlands.Cohomology.LinearHomComplex

open CategoryTheory Opposite
open CochainComplex.HomComplex

universe uR uC vC

variable (R : Type uR) [Ring R]
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]

/-- The actual module-valued complex of graded morphisms. -/
@[implicit_reducible]
def complex (P Q : CochainComplex C ℤ) : CochainComplex (ModuleCat.{vC} R) ℤ where
  X n := ModuleCat.of R (Cochain P Q n)
  d n m := ModuleCat.ofHom (δ_hom R P Q n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_shape n m h z
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_δ i j k z

variable {P P' P'' Q Q' Q'' : CochainComplex C ℤ}

/-- Precomposition by a chain map, on the actual module of graded cochains. -/
def precompLinear (f : P' ⟶ P) (Q : CochainComplex C ℤ) (n : ℤ) :
    Cochain P Q n →ₗ[R] Cochain P' Q n where
  toFun z := (Cochain.ofHom f).comp z (zero_add n)
  map_add' _ _ := Cochain.comp_add _ _ _ _
  map_smul' _ _ := Cochain.comp_smul _ _ _ _

/-- Postcomposition by a chain map, on the actual module of graded cochains. -/
def postcompLinear (P : CochainComplex C ℤ) (g : Q ⟶ Q') (n : ℤ) :
    Cochain P Q n →ₗ[R] Cochain P Q' n where
  toFun z := z.comp (Cochain.ofHom g) (add_zero n)
  map_add' _ _ := Cochain.add_comp _ _ _ _
  map_smul' _ _ := Cochain.smul_comp _ _ _ _

/-- Chain maps in both variables act by precomposition and postcomposition. -/
def map (f : P' ⟶ P) (g : Q ⟶ Q') :
    complex R P Q ⟶ complex R P' Q' where
  f n := ModuleCat.ofHom
    ((postcompLinear R P' g n).comp (precompLinear R f Q n))
  comm' n m _ := by
    ext z
    exact (δ_comp_ofHom ((Cochain.ofHom f).comp z (zero_add n)) g m).trans
      (congrArg (fun a => a.comp (Cochain.ofHom g) (add_zero m))
        (δ_ofHom_comp f z m))

@[simp]
theorem map_f_apply (f : P' ⟶ P) (g : Q ⟶ Q') (n : ℤ)
    (z : Cochain P Q n) (p q : ℤ) (hpq : p + n = q) :
    ((map R f g).f n z).v p q hpq = f.f p ≫ z.v p q hpq ≫ g.f q := by
  change (((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc]

@[simp]
theorem map_id (P Q : CochainComplex C ℤ) :
    map R (𝟙 P) (𝟙 Q) = 𝟙 (complex R P Q) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change ((map R (𝟙 P) (𝟙 Q)).f n z).v p q hpq = z.v p q hpq
  simpa only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id] using
    map_f_apply R (𝟙 P) (𝟙 Q) n z p q hpq

theorem map_comp (f : P' ⟶ P) (f' : P'' ⟶ P') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    map R f g ≫ map R f' g' = map R (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change ((map R f' g').f n ((map R f g).f n z)).v p q hpq =
    ((map R (f' ≫ f) (g ≫ g')).f n z).v p q hpq
  rw [map_f_apply R f' g', map_f_apply R f g,
    map_f_apply R (f' ≫ f) (g ≫ g')]
  simp only [HomologicalComplex.comp_f, Category.assoc]

/-- With the first complex fixed, the actual Hom-complex functor. -/
@[implicit_reducible]
def functor (P : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{vC} R) ℤ where
  obj Q := complex R P Q
  map g := map R (𝟙 P) g
  map_id Q := map_id R P Q
  map_comp f g := by
    simpa using (map_comp R (𝟙 P) (𝟙 P) f g).symm

/-- Contravariance in the first complex is an actual natural chain map. -/
def precompose (f : P' ⟶ P) : functor R P ⟶ functor R P' where
  app Q := map R f (𝟙 Q)
  naturality Q Q' g := by
    dsimp [functor]
    rw [map_comp, map_comp]
    simp

/-- The bifunctor preserves all differentials and chain maps in both variables. -/
def bifunctor :
    (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤
      CochainComplex (ModuleCat.{vC} R) ℤ where
  obj P := functor R P.unop
  map f := precompose R f.unop
  map_id P := by
    apply NatTrans.ext
    funext Q
    exact map_id R P.unop Q
  map_comp f g := by
    apply NatTrans.ext
    funext Q
    dsimp [precompose]
    simpa using (map_comp R f.unop g.unop (𝟙 Q) (𝟙 Q)).symm

/-- Cohomology of the actual Hom complex, without a derived-Ext identification. -/
def cohomology (P : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex C ℤ ⥤ ModuleCat.{vC} R :=
  functor R P ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{vC} R)
    (ComplexShape.up ℤ) n

/-- Precomposition descends to the constructed cohomology modules. -/
def precomposeCohomology (f : P' ⟶ P) (n : ℤ) :
    cohomology R P n ⟶ cohomology R P' n :=
  Functor.whiskerRight (precompose R f)
    (HomologicalComplex.homologyFunctor (ModuleCat.{vC} R) (ComplexShape.up ℤ) n)

end Langlands.Cohomology.LinearHomComplex
