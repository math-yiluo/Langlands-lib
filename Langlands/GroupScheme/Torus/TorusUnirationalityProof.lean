import Langlands.GroupScheme.Torus.WeilRestrictionRational
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.WeilRestrictionSplitNorm
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.CorepresentedComultiplication
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.TensorProduct.Pi

/-! # Rationality of induced tori and unirationality of tori over a field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace TorusUnirationality

section SplitWeilIso

variable (k L : Type u) [Field k] [Field L] [Algebra k L] (I : Type u) [Fintype I]

/-- The coordinate maps of `(I → L) ⊗[k] T` identify its units with families of units of
`L ⊗[k] T`. -/
theorem splitCoordUnits_bijective (T : Type u) [CommRing T] [Algebra k T] :
    Function.Bijective
      (MonoidHom.pi fun i => Units.map (WeilGm.splitCoord k L I T i).toMonoidHom) := by
  classical
  let Φ : (I → L) ⊗[k] T ≃ₐ[k] (I → L ⊗[k] T) :=
    (Algebra.TensorProduct.comm k (I → L) T).trans
      ((Algebra.TensorProduct.piRight k k T (fun _ : I => L)).trans
        (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.comm k T L))
  have hΦ : ∀ (x : (I → L) ⊗[k] T) (i : I), Φ x i = WeilGm.splitCoord k L I T i x := by
    intro x i
    induction x using TensorProduct.inductionOn with
    | tmul b t => simp [Φ]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  let E : ((I → L) ⊗[k] T)ˣ ≃* (I → (L ⊗[k] T)ˣ) :=
    (Units.mapEquiv Φ.toMulEquiv).trans MulEquiv.piUnits
  have hE : ⇑(MonoidHom.pi fun i => Units.map (WeilGm.splitCoord k L I T i).toMonoidHom) =
      ⇑E := by
    funext w
    funext i
    apply Units.ext
    exact (hΦ w i).symm
  rw [hE]
  exact E.bijective

variable (G : GroupScheme (Spec (CommRingCat.of L)))
  (σ : G ≅ splitTorus (Spec (CommRingCat.of L)) I)

/-- The point maps of the split Weil homomorphism are bijective. -/
theorem splitWeilPointHom_bijective (T : CommAlgCat.{u} (CommRingCat.of k)) :
    Function.Bijective (WeilGm.splitWeilPointHom k L I G σ T) := by
  have h1 := splitCoordUnits_bijective k L I T
  have h2 := (splitTorus.algebraPointsEquiv (R := CommRingCat.of L) I (L ⊗[k] T)).symm.bijective
  have h3 : Function.Bijective
      ((splitTorus (Spec (CommRingCat.of L)) I).affinePointsTarget σ.inv
        (CommAlgCat.of (CommRingCat.of L) (L ⊗[k] T))) := by
    let e : (splitTorus (Spec (CommRingCat.of L)) I).X ≅ G.X := (Grp.forget _).mapIso σ.symm
    have he : ⇑((splitTorus (Spec (CommRingCat.of L)) I).affinePointsTarget σ.inv
        (CommAlgCat.of (CommRingCat.of L) (L ⊗[k] T))) = ⇑((Iso.refl _).homCongr e) := by
      funext x
      exact (Category.id_comp _).symm
    rw [he]
    exact Equiv.bijective _
  exact h3.comp (h2.comp h1)

instance isIso_splitWeilNat : IsIso (WeilGm.splitWeilNat k L I G σ) := by
  have : ∀ T, IsIso ((WeilGm.splitWeilNat k L I G σ).app T) := fun T =>
    (ConcreteCategory.isIso_iff_bijective _).2 (splitWeilPointHom_bijective k L I G σ T)
  exact NatIso.isIso_of_isIso_app _

omit [Field k] in
theorem groupSchemeMap_id {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
    {B : CommAlgCat.{u} R} (c : (F ⋙ forget GrpCat).CorepresentableBy B) :
    Corepresented.groupSchemeMap c c (𝟙 F) = 𝟙 _ := by
  apply Corepresented.hom_ext_affinePoints
  intro S f
  rw [Corepresented.groupSchemeMap_affinePoints]
  rfl

variable [FiniteDimensional k L] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The split Weil homomorphism `Res_{(I → L)/k} 𝔾ₘ ⟶ Res_{L/k} G` is an isomorphism. -/
instance isIso_splitWeilHom : IsIso (WeilGm.splitWeilHom k L I G σ) := by
  let e := WeilGm.corepresentableBy (CommRingCat.of k) (I → L)
  let d := AffineWeil.corepresentableBy k L G
  let α := WeilGm.splitWeilNat k L I G σ
  refine ⟨Corepresented.groupSchemeMap d e (inv α), ?_, ?_⟩
  · change Corepresented.groupSchemeMap e d α ≫ Corepresented.groupSchemeMap d e (inv α) = 𝟙 _
    rw [Corepresented.groupSchemeMap_comp, IsIso.hom_inv_id, groupSchemeMap_id]
  · change Corepresented.groupSchemeMap d e (inv α) ≫ Corepresented.groupSchemeMap e d α = 𝟙 _
    rw [Corepresented.groupSchemeMap_comp, IsIso.inv_hom_id, groupSchemeMap_id]

end SplitWeilIso

/-- **Unirationality of tori.** Every torus over a field is unirational. -/
theorem isUnirational_of_isTorus (k : Type u) [Field k]
    (T : GroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T) :
    IsUnirational k T.X := by
  classical
  obtain ⟨L, _, _, _, _, hsplit⟩ := torusFiniteGaloisSplitting k T hT
  let Tc : CommGroupScheme (Spec (CommRingCat.of k)) := { T with comm := hT.isCommMonObj }
  have : IsAffine Tc.X.left := SplittingAssembly.isAffine_of_isTorus T hT
  have hTL : IsTorus (GaloisPointComparison.baseChanged k L Tc.toGrp) := hsplit.isTorus
  have : IsAffine (GaloisPointComparison.baseChanged k L Tc.toGrp).X.left :=
    SplittingAssembly.isAffine_of_isTorus _ hTL
  have : Smooth (GaloisPointComparison.baseChanged k L Tc.toGrp).X.hom := hTL.smooth
  have hsm : Smooth (GaloisNorm.norm k L Tc).hom.hom.left :=
    GaloisNormSmoothnessProof.galoisNormSmoothness k L Tc hsplit
  obtain ⟨I, _, ⟨σ⟩⟩ := hsplit
  let _ : Fintype I := Fintype.ofFinite I
  let s := WeilGm.splitWeilHom k L I (GaloisPointComparison.baseChanged k L Tc.toGrp) σ
  let N := GaloisNorm.norm k L Tc
  have hW : IsUnirational k (WeilGm.groupScheme (CommRingCat.of k) (I → L)).X :=
    (WeilGmRational.hasFiniteAffineBirationalModel k (I → L)).isUnirational
  have hs : IsIso s.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) s
  have hopen : IsOpenMap (s.hom.hom.left ≫ N.hom.hom.left) := by
    rw [Scheme.Hom.comp_base]
    exact N.hom.hom.left.isOpenMap.comp s.hom.hom.left.isOpenMap
  have : IsIntegral T.X.left := hT.isIntegral
  obtain ⟨x⟩ := WeilGmRational.nonempty_left k (I → L)
  exact hW.map (s ≫ N).hom.hom (hopen.isOpen_range.dense ⟨_, x, rfl⟩)

end TorusUnirationality

open TorusUnirationality in
/-- **Unirationality of tori** (Milne, *Algebraic Groups* (2017), Propositions 12.60 and
12.64): Weil-restricted multiplicative groups and induced tori are rational, and every torus
over a field is unirational. -/
theorem torusUnirationality : TorusUnirationalityStatement.{u} := by
  intro k _
  exact ⟨fun k' _ _ _ => WeilGmRational.hasFiniteAffineBirationalModel k k',
    fun T hT => isUnirational_of_isTorus k T hT,
    fun A _ _ _ _ => WeilGmRational.hasFiniteAffineBirationalModel k A⟩

end Langlands.GroupScheme
