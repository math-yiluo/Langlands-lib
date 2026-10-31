import Langlands.AbelianScheme.PointedMorphismRigidity
import Langlands.AbelianScheme.FieldPointedMorphismRigidityProof
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.AbelianScheme

private theorem pointwise_eq_of_fiber_map_eq {S : Scheme.{u}} {X Y : Over S}
    (f g : X ⟶ Y)
    (h : ∀ s : S, (Over.pullback (S.fromSpecResidueField s)).map f =
      (Over.pullback (S.fromSpecResidueField s)).map g) :
    ∀ x : X.left, f.left x = g.left x := by
  intro x
  have hh := congrArg (fun k => k.left ≫ Limits.pullback.fst Y.hom
    (S.fromSpecResidueField (X.hom x))) (h (X.hom x))
  simp only [Over.pullback_map_left, Limits.pullback.lift_fst] at hh
  have hh' := congrArg (fun k : X.hom.fiber (X.hom x) ⟶ Y.left => k (X.hom.asFiber x)) hh
  change f.left (X.hom.fiberι _ (X.hom.asFiber x)) =
    g.left (X.hom.fiberι _ (X.hom.asFiber x)) at hh'
  simpa only [Scheme.Hom.fiberι_asFiber] using hh'

private theorem isMonHom_of_defect_eq_one {S : Scheme.{u}}
    (A H : GroupScheme S) (f : A.X ⟶ H.X) (hf : η[A.X] ≫ f = η[H.X])
    (hd : (μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f)) = 1) :
    IsMonHom f := by
  refine ⟨hf, ?_⟩
  have hm := div_eq_one.mp hd
  rw [CategoryTheory.Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp] at hm
  exact hm

private theorem defect_section {S : Scheme.{u}}
    (A H : GroupScheme S) (f : A.X ⟶ H.X) (hf : η[A.X] ≫ f = η[H.X]) :
    lift η[A.X] η[A.X] ≫
      ((μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))) = 1 := by
  have hf' : (1 : 𝟙_ (Over S) ⟶ A.X) ≫ f = 1 := by
    simpa only [← MonObj.one_eq_one] using hf
  simp [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, hf',
    MonObj.mul_eq_mul, MonObj.one_eq_one]

set_option synthInstance.maxHeartbeats 40000 in
private theorem map_defect_eq_one {S T : Scheme.{u}} (b : T ⟶ S)
    (A H : GroupScheme S) (f : A.X ⟶ H.X)
    [IsMonHom ((Over.pullback b).map f)] :
    (Over.pullback b).map
      ((μ[A.X] ≫ f) / ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))) = 1 := by
  simp only [div_eq_mul_inv, MonObj.mul_eq_mul, Functor.map_comp, Functor.map_mul,
    Functor.map_inv', MonObj.mul_comp, mul_inv_cancel]

/-- Every unit-preserving morphism in the arbitrary-base rigidity statement
preserves multiplication. -/
theorem pointedMorphismRigidity : PointedMorphismRigidity.{u} := by
  intro S A H hA hHfp hHqc hHqs f hf
  let : Smooth A.X.hom := hA.1
  let : IsProper A.X.hom := hA.2.1
  let : GeometricallyConnected A.X.hom := hA.2.2
  let : LocallyOfFinitePresentation H.X.hom := hHfp
  let : QuasiCompact H.X.hom := hHqc
  let : QuasiSeparated H.X.hom := hHqs
  let P := A.X ⊗ A.X
  let e : 𝟙_ (Over S) ⟶ P := lift η[A.X] η[A.X]
  let d : P ⟶ H.X := (μ[A.X] ≫ f) /
    ((fst A.X A.X ≫ f) * (snd A.X A.X ≫ f))
  have he : e.left ≫ P.hom = 𝟙 S := e.w
  have hed : e ≫ d = 1 := defect_section A H f hf
  have hed' : e.left ≫ d.left = η[H.X].left := by
    change (e ≫ d).left = η[H.X].left
    rw [hed, ← MonObj.one_eq_one]
  have hfiber : ∀ s : S,
      (Over.pullback (S.fromSpecResidueField s)).map d =
      (Over.pullback (S.fromSpecResidueField s)).map (1 : P ⟶ H.X) := by
    intro s
    let F := Over.pullback (S.fromSpecResidueField s)
    let As := F.mapGrp.obj A
    let Hs := F.mapGrp.obj H
    have hAs : GroupScheme.IsAbelian As := by
      refine ⟨?_, ?_, ?_⟩
      · change Smooth (Limits.pullback.snd A.X.hom (S.fromSpecResidueField s))
        infer_instance
      · change IsProper (Limits.pullback.snd A.X.hom (S.fromSpecResidueField s))
        infer_instance
      · change GeometricallyConnected
          (Limits.pullback.snd A.X.hom (S.fromSpecResidueField s))
        infer_instance
    have hfs : η[As.X] ≫ F.map f = η[Hs.X] := by
      change η[F.obj A.X] ≫ F.map f = η[F.obj H.X]
      simp only [Functor.obj.η_def, Category.assoc, ← Functor.map_comp, hf]
    have : IsMonHom (F.map f) :=
      fieldPointedMorphismRigidity (S.residueField s) As Hs hAs
        (by change LocallyOfFinitePresentation
              (Limits.pullback.snd H.X.hom (S.fromSpecResidueField s)); infer_instance)
        (by change QuasiCompact
              (Limits.pullback.snd H.X.hom (S.fromSpecResidueField s)); infer_instance)
        (by change QuasiSeparated
              (Limits.pullback.snd H.X.hom (S.fromSpecResidueField s)); infer_instance)
        (F.map f) hfs
    rw [Functor.map_one]
    exact map_defect_eq_one (S.fromSpecResidueField s) A H f
  have htop := pointwise_eq_of_fiber_map_eq d (1 : P ⟶ H.X) hfiber
  have hPsm : Smooth P.hom := by
    change Smooth (Limits.pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
    infer_instance
  have hPpr : IsProper P.hom := by
    change IsProper (Limits.pullback.fst A.X.hom A.X.hom ≫ A.X.hom)
    infer_instance
  have hPgc : GeometricallyConnected P.hom :=
    GeometricallyConnected.comp (Limits.pullback.fst A.X.hom A.X.hom) A.X.hom
  have hdfactor := Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions
    P.left S H.X.left P.hom e.left d.left he
    (Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
      P.left S P.hom hPsm hPpr hPgc) (fun x => by
      rw [hed']
      exact htop x)
  apply isMonHom_of_defect_eq_one A H f hf
  change d = 1
  apply Over.OverMorphism.ext
  change d.left = P.hom ≫ η[H.X].left
  simpa only [hed'] using hdfactor

end Langlands.AbelianScheme
