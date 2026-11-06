import Langlands.GroupScheme.Rational.FiniteGaloisFormReductiveStatement
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Connected reductivity of finite-Galois forms

Local group isomorphisms on the points of a cover `U` give, for every point of `U` over a base
change `S' → S`, an isomorphism of the base-changed group schemes. Over the cover
`Spec L → Spec K` of a finite Galois extension this identifies `G_L` with `H_L` and, through
an embedding of `L` into an algebraic closure of `K`, the geometric fibres of `G` and `H`.
Smoothness and affineness then descend from `H_L` to `H`, connectedness passes from `H_L` to
its image `H`, and the geometric unipotent radical of `H` is that of `G`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S S' : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- The point of the cover over `(Over.map b).obj T` induced by a point `p` of the cover
over `b`. -/
def basePoint (b : S' ⟶ S) (p : Over.mk b ⟶ U) (T : Over S') : (Over.map b).obj T ⟶ U :=
  (Over.homMk T.hom rfl : (Over.map b).obj T ⟶ Over.mk b) ≫ p

theorem basePoint_naturality (b : S' ⟶ S) (p : Over.mk b ⟶ U) {T T' : Over S'}
    (a : T' ⟶ T) : (Over.map b).map a ≫ basePoint b p T = basePoint b p T' := by
  rw [basePoint, basePoint, ← Category.assoc]
  congr 1
  ext
  simp

/-- A point `p` of the cover over `b : S' ⟶ S` turns natural local group isomorphisms into an
isomorphism of the base changes along `b`. -/
def baseChangeIso (e : LocalGroupIso G H U) (b : S' ⟶ S) (p : Over.mk b ⟶ U) :
    (GroupScheme.baseChange b).obj G ≅ (GroupScheme.baseChange b).obj H :=
  isoOfPoints (fun T => (baseChangePointsEquiv b G T).trans
      ((e.toFun (basePoint b p T)).trans (baseChangePointsEquiv b H T).symm))
    (fun {T T'} a x => by
      apply (baseChangePointsEquiv b H T').injective
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_naturality,
        MulEquiv.apply_symm_apply, ← basePoint_naturality b p a, e.naturality])

end LocalGroupIso

/-- **Connected reductivity passes to finite-Galois forms.** -/
theorem finiteGaloisFormConnectedReductive :
    FiniteGaloisFormConnectedReductiveStatement.{u} := by
  intro K L _ _ _ _ _ G H e hG
  let b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc K L
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  -- The isomorphism `G_L ≅ H_L` at the tautological point of the cover.
  let eL := e.baseChangeIso b (𝟙 _)
  have : IsIso eL.inv.hom.hom.left := isIso_left_of_iso eL.symm
  have hwL : ((GroupScheme.baseChange b).obj H).X.hom =
      eL.inv.hom.hom.left ≫ ((GroupScheme.baseChange b).obj G).X.hom :=
    (Over.w eL.inv.hom.hom).symm
  -- Smoothness descends along `Spec L → Spec K`.
  have hsmooth : Smooth H.X.hom := by
    have : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
      inferInstanceAs (Smooth (pullback.snd G.X.hom b))
    have h2 : Smooth (pullback.snd H.X.hom b) := by
      change Smooth ((GroupScheme.baseChange b).obj H).X.hom
      rw [hwL]
      infer_instance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := H.X.hom) (g := b)
      ⟨⟨hsurj, hflat⟩, hqc⟩ h2
  -- Affineness descends along the field extension.
  have haffine : IsAffineHom H.X.hom := by
    have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    have : IsAffine ((GroupScheme.baseChange b).obj G).X.left :=
      inferInstanceAs (IsAffine (pullback G.X.hom b))
    have hbase : IsAffine (pullback H.X.hom b) := by
      change IsAffine ((GroupScheme.baseChange b).obj H).X.left
      exact IsAffine.of_isIso eL.inv.hom.hom.left
    have : IsAffine H.X.left :=
      Langlands.AlgebraicGeometry.fieldExtensionAffineDescent K L H.X.left H.X.hom hbase
    infer_instance
  -- Connectedness: `H_L ≅ G_L` is connected and surjects onto `H`.
  have hconn : ConnectedSpace H.X.left := by
    have : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
      G.connectedSpace_baseChange_of_smooth_affine b
    have hHL : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left := by
      let φ := Scheme.homeoOfIso (asIso eL.inv.hom.hom.left)
      exact φ.symm.surjective.connectedSpace φ.symm.continuous
    have : ConnectedSpace (pullback H.X.hom b : Scheme.{u}) := hHL
    have : Surjective (pullback.fst H.X.hom b) := inferInstance
    exact (pullback.fst H.X.hom b).surjective.connectedSpace
      (pullback.fst H.X.hom b).continuous
  -- The geometric unipotent radical: embed `L` into an algebraic closure of `K`.
  let κ : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let p : Over.mk (toAlgebraicClosure K) ⟶ Over.mk b :=
    Over.homMk (Spec.map (CommRingCat.ofHom κ.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom κ.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact κ.commutes x)
  let eK := e.baseChangeIso (toAlgebraicClosure K) p
  exact ⟨hsmooth, haffine, hconn,
    HasTrivialUnipotentRadical.of_iso eK.symm hG.hasTrivialGeometricUnipotentRadical⟩

end Langlands.GroupScheme
