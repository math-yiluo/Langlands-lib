import Langlands.Sheaf.Godement
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Godement constructions on the small etale site of an actual scheme

For every point `x` of a scheme, use a separable closure of its residue field.
The resulting geometric points define the actual degree-zero Godement functor
and its functorial cokernel complex for module-valued etale sheaves.
-/

noncomputable section

namespace Langlands.Geometry.EtaleGodement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (X : Scheme.{u})

/-- The geometric point over `x` obtained from its separably closed residue field. -/
def geometricPoint (x : X) : GrothendieckTopology.Point.{u} (Scheme.smallEtaleTopology X) :=
  Scheme.pointSmallEtale
    ((Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩)

/-- These are genuine enough geometric points, not an assumed fiber assignment. -/
theorem geometricPoints_conservative :
    (ObjectProperty.ofObj (geometricPoint X)).IsConservativeFamilyOfPoints :=
  Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X

variable (R : Type u) [CommRing R]

/-- Evaluation at `1` corepresents the underlying-set functor on modules. -/
def moduleForgetCorepresentable :
    (forget (ModuleCat.{u} R)).CorepresentableBy (ModuleCat.of R R) where
  homEquiv {Y} :=
    ConcreteCategory.homEquiv.trans (LinearMap.ringLmapEquivSelf R R Y).toEquiv
  homEquiv_comp _ _ := rfl

/-- Forgetting the module structure preserves the sheaf condition even on this large site. -/
instance moduleSheafCompose :
    (Scheme.smallEtaleTopology X).HasSheafCompose (forget (ModuleCat.{u} R)) where
  isSheaf P hP := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso _ (Functor.isoWhiskerLeft P
      (moduleForgetCorepresentable R).toIso) (hP (ModuleCat.of R R))

/-- Module-valued sheaves on the actual small etale site of `X`. -/
abbrev EtaleSheaf :=
  CategoryTheory.Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)

/-- Degree zero is the product of skyscrapers of geometric fibers. -/
def zeroFunctor : EtaleSheaf X R ⥤ EtaleSheaf X R :=
  Langlands.Sheaf.Godement.zeroFunctor (geometricPoint X) (ModuleCat.{u} R)

/-- The canonical map from an etale sheaf to its degree-zero Godement object. -/
def coaugmentation : 𝟭 (EtaleSheaf X R) ⟶ zeroFunctor X R :=
  Langlands.Sheaf.Godement.coaugmentation (geometricPoint X) (ModuleCat.{u} R)

/-- The genuine geometric fibers separate morphisms of etale module sheaves. -/
theorem fibers_jointlyFaithful :
    JointlyFaithful
      (fun x : X => (geometricPoint X x).sheafFiber (A := ModuleCat.{u} R)) := by
  constructor
  intro F G f g h
  apply ((geometricPoints_conservative X).jointlyFaithful (ModuleCat.{u} R)).map_injective
  intro p
  obtain ⟨x, hx⟩ :=
    (ObjectProperty.ofObj_iff (geometricPoint X) p.obj).mp p.property
  exact hx ▸ h x

/-- The canonical degree-zero map is an embedding, proved from geometric points. -/
instance (F : EtaleSheaf X R) : Mono ((coaugmentation X R).app F) :=
  Langlands.Sheaf.Godement.mono_coaugmentation_of_jointlyFaithful
    (geometricPoint X) (ModuleCat.{u} R) (fibers_jointlyFaithful X R) F

/-- The resulting actual functor from etale sheaves to cochain complexes. -/
def complexFunctor : EtaleSheaf X R ⥤ CochainComplex (EtaleSheaf X R) ℕ :=
  Langlands.Sheaf.Godement.complexFunctor (geometricPoint X) (ModuleCat.{u} R)

/-- The Godement complex on the small etale site with module coefficients. -/
abbrev complex (F : EtaleSheaf X R) : CochainComplex (EtaleSheaf X R) ℕ :=
  (complexFunctor X R).obj F

end Langlands.Geometry.EtaleGodement
