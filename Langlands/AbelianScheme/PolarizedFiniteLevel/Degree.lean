import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Constant degree and its transport for polarized finite-level data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {X Y Z W S T : Scheme.{u}}

/-- Constant degree measured by the native finite-flat rank of the actual map. -/
def HasConstantDegree (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ y, f.finrank y = r

/-- Postcomposition with an isomorphism transports the native rank function. -/
lemma finrank_comp_iso (f : X ⟶ Y) [Flat f] [IsFinite f] (e : Y ≅ Z) (z : Z) :
    (f ≫ e.hom).finrank z = f.finrank (e.inv z) := by
  apply Scheme.Hom.finrank_of_isPullback (𝟙 X) (f ≫ e.hom) f e.inv
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

lemma HasConstantDegree.pre_iso {f : X ⟶ Y} [Flat f] [IsFinite f]
    {r : ℕ} (h : HasConstantDegree f r) (e : Z ≅ X) :
    HasConstantDegree (e.hom ≫ f) r := by
  intro y
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  exact h y

lemma HasConstantDegree.post_iso {f : X ⟶ Y} [Flat f] [IsFinite f]
    {r : ℕ} (h : HasConstantDegree f r) (e : Y ≅ Z) :
    HasConstantDegree (f ≫ e.hom) r := by
  intro z
  rw [finrank_comp_iso]
  exact h (e.inv z)

lemma hasConstantDegree_pre_iso_iff (f : X ⟶ Y) [Flat f] [IsFinite f]
    (e : Z ≅ X) (r : ℕ) :
    HasConstantDegree (e.hom ≫ f) r ↔ HasConstantDegree f r := by
  refine ⟨fun h => ?_, fun h => h.pre_iso e⟩
  simpa using h.pre_iso e.symm

lemma hasConstantDegree_post_iso_iff (f : X ⟶ Y) [Flat f] [IsFinite f]
    (e : Y ≅ Z) (r : ℕ) :
    HasConstantDegree (f ≫ e.hom) r ↔ HasConstantDegree f r := by
  refine ⟨fun h => ?_, fun h => h.post_iso e⟩
  simpa [Category.assoc] using h.post_iso e.symm

/-- Native degree is preserved by any Cartesian square of schemes. -/
lemma HasConstantDegree.of_isPullback {f : X ⟶ Y} [Flat f] [IsFinite f]
    {fst : W ⟶ X} {snd : W ⟶ Z} {g : Z ⟶ Y}
    (sq : IsPullback fst snd f g) {r : ℕ} (h : HasConstantDegree f r) :
    HasConstantDegree snd r := by
  intro z
  rw [Scheme.Hom.finrank_of_isPullback fst snd f g sq]
  exact h (g z)

/-- Constant native rank is the affine-local module rank on spectra. -/
lemma hasConstantDegree_spec_iff {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (hf : f.hom.Finite) (hflat : f.hom.Flat) (r : ℕ) :
    HasConstantDegree (Spec.map f) r ↔ ∀ p, f.hom.finrank p = r := by
  change (∀ p : PrimeSpectrum R, (Spec.map f).finrank p = r) ↔ _
  simp only [Scheme.Hom.finrank_SpecMap_eq_finrank hf hflat]

variable {A B C D : AbelianScheme S}

/-- Degree `d²` of an actual abelian-scheme homomorphism. -/
def HasDegreeSquare (f : A ⟶ B) (d : ℕ) : Prop :=
  HasConstantDegree (hom f) (d ^ 2)

/-- The actual scheme isomorphism underlying an abelian-scheme isomorphism. -/
def underlyingSchemeIso (e : A ≅ B) : A.X.left ≅ B.X.left where
  hom := hom e.hom
  inv := hom e.inv
  hom_inv_id := by rw [← hom_comp, e.hom_inv_id, hom_id]
  inv_hom_id := by rw [← hom_comp, e.inv_hom_id, hom_id]

lemma HasDegreeSquare.pre_iso {f : A ⟶ B} (hf : IsIsogeny f)
    {d : ℕ} (h : HasDegreeSquare f d) (e : C ≅ A) :
    HasDegreeSquare (e.hom ≫ f) d := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  exact HasConstantDegree.pre_iso h (underlyingSchemeIso e)

lemma HasDegreeSquare.post_iso {f : A ⟶ B} (hf : IsIsogeny f)
    {d : ℕ} (h : HasDegreeSquare f d) (e : B ≅ C) :
    HasDegreeSquare (f ≫ e.hom) d := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  exact HasConstantDegree.post_iso h (underlyingSchemeIso e)

lemma hasDegreeSquare_iso_iff (f : A ⟶ B) (hf : IsIsogeny f)
    (e : C ≅ A) (e' : B ≅ D) (d : ℕ) :
    HasDegreeSquare (e.hom ≫ f ≫ e'.hom) d ↔ HasDegreeSquare f d := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  change HasConstantDegree
    (hom e.hom ≫ hom f ≫ hom e'.hom) (d ^ 2) ↔ HasConstantDegree (hom f) (d ^ 2)
  rw [← Category.assoc]
  have : IsIso (hom e.hom) := (underlyingSchemeIso e).isIso_hom
  exact (hasConstantDegree_post_iso_iff (hom e.hom ≫ hom f)
    (underlyingSchemeIso e') (d ^ 2)).trans
      (hasConstantDegree_pre_iso_iff (hom f) (underlyingSchemeIso e) (d ^ 2))

/-- The degree of an isogeny is a locally constant native rank on a noetherian base. -/
lemma isLocallyConstant_finrank_of_isIsogeny [IsLocallyNoetherian S]
    (f : A ⟶ B) (hf : IsIsogeny f) :
    IsLocallyConstant (hom f).finrank := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  let : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  exact Scheme.Hom.isLocallyConstant_finrank (hom f)

/-- The square defining the changed actual abelian-scheme homomorphism is Cartesian. -/
lemma hom_baseChange_isPullback (b : T ⟶ S) (f : A ⟶ B) :
    IsPullback (pullback.fst A.X.hom b) (hom ((baseChange b).map f))
      (hom f) (pullback.fst B.X.hom b) := by
  change IsPullback (pullback.fst A.X.hom b)
    ((Over.pullback b).map (groupHom f).hom.hom).left
    (hom f) (pullback.fst B.X.hom b)
  have h : IsPullback (pullback.fst A.X.hom b)
      (((Over.pullback b).map (groupHom f).hom.hom).left ≫ pullback.snd B.X.hom b)
      (hom f ≫ B.X.hom) b := by
    rw [show ((Over.pullback b).map (groupHom f).hom.hom).left ≫
      pullback.snd B.X.hom b = pullback.snd A.X.hom b from
        ((Over.pullback b).map (groupHom f).hom.hom).w, (groupHom f).hom.hom.w]
    exact IsPullback.of_hasPullback A.X.hom b
  apply h.of_bot _ (IsPullback.of_hasPullback B.X.hom b)
  change pullback.fst A.X.hom b ≫ (groupHom f).hom.hom.left = _
  simp

/-- Isogeny degree is preserved by arbitrary actual base change. -/
lemma HasDegreeSquare.baseChange {f : A ⟶ B} (hf : IsIsogeny f)
    {d : ℕ} (h : HasDegreeSquare f d) (b : T ⟶ S) :
    HasDegreeSquare ((baseChange b).map f) d := by
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  exact h.of_isPullback (hom_baseChange_isPullback b f)

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable (compatibility : DualAbelianBaseChangeStatement.{u})
variable (b : T ⟶ S) (A : AbelianScheme S)
variable (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (hA' : HasDualScheme ((AbelianScheme.baseChange b).obj A))
variable (geometryA' : DualSchemeGeometry ((AbelianScheme.baseChange b).obj A) hA')
variable (MA' : LineBundle ((relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).obj
  (dualScheme ((AbelianScheme.baseChange b).obj A) hA')))
variable (evaluationA' : tensorObj
  (poincareFamily ((AbelianScheme.baseChange b).obj A) hA').obj.carrier
  MA'.obj ≅ structureSheaf ((relativeSpace ((AbelianScheme.baseChange b).obj A).X.hom).obj
    (dualScheme ((AbelianScheme.baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- Canonical transport to the changed dual preserves constant polarization degree. -/
lemma HasDegreeSquare.dualAbelianBaseChangeMap (lam : A ⟶ DA)
    (hf : IsIsogeny lam) {d : ℕ} (h : HasDegreeSquare lam d) :
    HasDegreeSquare
      (AbelianScheme.dualAbelianBaseChangeMap preservation stability composition
        unitCoherence associativity
        comparison symmetry universality compatibility b A hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' lam) d := by
  exact HasDegreeSquare.post_iso (hf.baseChange b) (HasDegreeSquare.baseChange hf h b)
    (dualAbelianBaseChangeIso preservation stability composition unitCoherence associativity
      comparison symmetry universality compatibility b A hA geometryA MA evaluationA
      hA' geometryA' MA' evaluationA')

end Langlands.AbelianScheme.PolarizedFiniteLevel
