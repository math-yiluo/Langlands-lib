import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Reductive group schemes at field-valued points and under base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- The actual residue-field fibre of a reductive group scheme is connected reductive. -/
theorem IsReductive.isConnectedReductive_residueFiber (hG : IsReductive G) (s : S) :
    IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G) := by
  have hbar := (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed
  apply IsConnectedReductive.of_fieldExtension
    (k := S.residueField s) (K := AlgebraicClosure (S.residueField s))
  exact hbar.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure _) G).symm

/-- Every actual field-valued point of the base of a reductive group has
a connected reductive pullback. -/
theorem IsReductive.isConnectedReductive_baseChange (hG : IsReductive G)
    {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    IsConnectedReductive ((baseChange f).obj G) := by
  let s := f (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo f)
  let : Algebra (S.residueField s) k := φ.hom.toAlgebra
  have hκ := hG.isConnectedReductive_residueFiber s
  have hk := connectedReductiveFieldExtensionStatement (S.residueField s) k
    ((baseChange (S.fromSpecResidueField s)).obj G) hκ
  have h := hk.of_iso (baseChangeCompIso (S.fromSpecResidueField s) (Spec.map φ) G)
  have hfactor : Spec.map φ ≫ S.fromSpecResidueField s = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S f
  rwa [hfactor] at h

/-- In particular, every algebra-valued field fibre over an affine base is
connected reductive. -/
theorem IsReductive.isConnectedReductive_algebraMap
    {R : Type u} [CommRing R] {H : GroupScheme (Spec (CommRingCat.of R))}
    (hH : IsReductive H) (k : Type u) [Field k] [Algebra R k] :
    IsConnectedReductive ((baseChange (Spec.algebraMap R k)).obj H) :=
  hH.isConnectedReductive_baseChange (Spec.algebraMap R k)

set_option backward.isDefEq.respectTransparency.types false in
/-- Reductivity of an actual group scheme is preserved by arbitrary scheme base change. -/
theorem IsReductive.baseChange (hG : IsReductive G) (b : S' ⟶ S) :
    IsReductive ((baseChange b).obj G) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  refine ⟨?_, ?_, fun s' => ?_⟩
  · change Smooth (pullback.snd G.X.hom b)
    infer_instance
  · change IsAffineHom (pullback.snd G.X.hom b)
    exact MorphismProperty.pullback_snd _ _ hG.isAffineHom
  · have h := hG.isConnectedReductive_baseChange (geometricPoint S' s' ≫ b)
    exact (h.of_iso (baseChangeCompIso b (geometricPoint S' s') G).symm).isPseudoReductive

/-- Pull a reductive group scheme to an actual field-valued point, retaining the
actual pullback and its connected reductivity. -/
def reductiveFieldFiber {k : Type u} [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
    {H : GroupScheme S // IsReductive H} →
      {H : GroupScheme (Spec (CommRingCat.of k)) // IsConnectedReductive H} :=
  fun H => ⟨(baseChange f).obj H.val, H.property.isConnectedReductive_baseChange f⟩

@[simp]
theorem reductiveFieldFiber_val {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ S) (H : {H : GroupScheme S // IsReductive H}) :
    (reductiveFieldFiber f H).val = (baseChange f).obj H.val := rfl

/-- Pull a reductive group scheme along an arbitrary scheme morphism, retaining
the actual pullback and its reductivity. -/
def reductiveBaseChange (b : S' ⟶ S) :
    {H : GroupScheme S // IsReductive H} →
      {H : GroupScheme S' // IsReductive H} :=
  fun H => ⟨(baseChange b).obj H.val, H.property.baseChange b⟩

@[simp]
theorem reductiveBaseChange_val (b : S' ⟶ S)
    (H : {H : GroupScheme S // IsReductive H}) :
    (reductiveBaseChange b H).val = (baseChange b).obj H.val := rfl

end Langlands.GroupScheme
