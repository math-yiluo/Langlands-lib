import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions
import Langlands.AlgebraicGeometry.Modules.CechResolution.Exact
import Langlands.AlgebraicGeometry.OrderedAffineCoverCompact
import Mathlib.Topology.QuasiSeparated

/-! # Scalar sections of line bundles on quasi-compact quasi-separated schemes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

private lemma isIso_left_of_leftExact {C : Type*} [Category* C] [Abelian C]
    {A B : ShortComplex C} (t : A ⟶ B) (hA : A.Exact)
    [Mono A.f] [Mono B.f] [IsIso t.τ₂] [IsIso t.τ₃] : IsIso t.τ₁ := by
  have hk : (B.f ≫ inv t.τ₂) ≫ A.g = 0 := by
    rw [← cancel_mono t.τ₃, Category.assoc, Category.assoc,
      ← t.comm₂₃, IsIso.inv_hom_id_assoc, B.zero, zero_comp]
  let v := hA.lift (B.f ≫ inv t.τ₂) hk
  have hv : v ≫ A.f = B.f ≫ inv t.τ₂ := hA.lift_f _ hk
  refine ⟨⟨v, ?_, ?_⟩⟩
  · rw [← cancel_mono A.f, Category.assoc, hv, ← Category.assoc,
      t.comm₁₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono B.f, Category.assoc, t.comm₁₂, ← Category.assoc,
      hv, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover)

/-- A nonempty finite affine-cover intersection is compact on a quasi-separated scheme. -/
lemma isCompact_inter_of_quasiSeparated [QuasiSeparatedSpace X]
    (p : ℕ) (s : 𝒰.Idx p) : IsCompact (𝒰.inter s : Set X) := by
  have h := QuasiSeparatedSpace.isCompact_sInter_of_nonempty
    (s := Set.range (fun j : Fin (p + 1) => (𝒰.U (s.1 j) : Set X)))
    (Set.finite_range _) ⟨_, ⟨0, rfl⟩⟩
    (by rintro _ ⟨j, rfl⟩; exact Or.inl (𝒰.U (s.1 j)).isOpen)
    (by rintro _ ⟨j, rfl⟩; exact (𝒰.isAffineOpen (s.1 j)).isCompact)
  simpa only [Set.sInter_range, Scheme.OrderedAffineCover.inter,
    Opens.coe_iInf] using h

/-- Every nonempty affine-cover intersection is separated as an absolute scheme. -/
lemma isSeparated_inter (p : ℕ) (s : 𝒰.Idx p) :
    (𝒰.inter s : Scheme).IsSeparated := by
  let U := 𝒰.U (s.1 0)
  let : IsAffine (U : Scheme) := 𝒰.isAffineOpen (s.1 0)
  let j := X.homOfLE (𝒰.inter_le s 0)
  exact ⟨by
    rw [← terminal.comp_from j]
    infer_instance⟩

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
  (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (g : Y ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)
  [IsAffineHom g] [QuasiSeparatedSpace X] (L : LineBundle X)

/-- The separated scalar sections comparison applies to each compact cover intersection. -/
lemma isIso_scalarFactorSectionsMap_inverseImageCover_lineBundle_qcqs
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat)
    (p : ℕ) (s : 𝒰.Idx p) :
    IsIso (scalarFactorSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj)
        (inverseImageCover_inter_le g 𝒰 s)) := by
  let W := 𝒰.inter s
  let W' := (inverseImageCover g 𝒰).inter s
  let hW := inverseImageCover_inter_le g 𝒰 s
  have he : W' = g ⁻¹ᵁ W := inverseImageCover_inter g 𝒰 s
  let k := g.resLE W W' hW
  have hk : IsPullback k (W'.ι ≫ f') (W.ι ≫ f) (Spec.map φ) :=
    isPullback_resLE_baseChange g hW φ f f' h he
  let : IsAffineHom k :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hk.flip inferInstance
  let : CompactSpace (W : Scheme) :=
    isCompact_iff_compactSpace.mp (isCompact_inter_of_quasiSeparated 𝒰 p s)
  let : (W : Scheme).IsSeparated := isSeparated_inter 𝒰 p s
  let LW := (LineBundle.pullback W.ι).obj L
  let : IsIso (scalarSectionsBaseChangeMap φ (W.ι ≫ f) (W'.ι ≫ f') k
      (square_restrict_comm φ f f' g w W.ι W'.ι k (g.resLE_comp_ι hW))
        ((Scheme.Modules.pullback W.ι).obj L.obj)) :=
    isIso_scalarSectionsBaseChangeMap_lineBundle φ (W.ι ≫ f) (W'.ι ≫ f') k
      (square_restrict_comm φ f f' g w W.ι W'.ι k (g.resLE_comp_ι hW)) LW hk hφ
  have : IsIso (scalarFactorSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) hW ≫
        (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj L.obj) W').hom) := by
    rw [scalarFactorSectionsMap_pullbackUnit_comp g L.obj hW φ f f' w k
      (g.resLE_comp_ι hW)]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj L.obj) W').hom

/-- The canonical scalar Čech sections map is invertible in each degree for line bundles on
a quasi-separated scheme. Only sections, rather than derived sections, are used here. -/
lemma isIso_scalarCechSectionsMap_f_lineBundle_qcqs
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) (p : ℕ) :
    IsIso ((scalarCechSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒰).f p) :=
  isIso_scalarCechSectionsMap_f_of_factors φ f f' g w
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒰 p
      (fun s => isIso_scalarFactorSectionsMap_inverseImageCover_lineBundle_qcqs
        𝒰 φ f f' g w L h hφ p s)

omit [QuasiSeparatedSpace X] in
/-- The ordinary degree-zero augmentation commutes with the canonical scalar sections maps. -/
lemma scalarSectionsBaseChangeMap_augmentation :
    scalarSectionsBaseChangeMap φ f f' g w L.obj ≫
        (relativeGlobalSections f').map
          (augmentation (inverseImageCover g 𝒰) ((Scheme.Modules.pullback g).obj L.obj)) =
      (ModuleCat.extendScalars φ.hom).map
          ((relativeGlobalSections f).map (augmentation 𝒰 L.obj)) ≫
        (scalarCechSectionsMap φ f f' g w
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒰).f 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul,
    scalarSectionsBaseChangeMap_one_tmul, scalarCechSectionsMap]
  erw [scalarResolutionSectionsBaseChangeMap_one_tmul]
  have hm := congrArg (fun a => a.app ⊤ m)
    (augmentation_cechTermPushforward g
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒰)
  exact hm.symm

/-- Flat affine base change commutes with actual line-bundle sections on a quasi-compact
quasi-separated scheme, without a separatedness hypothesis. -/
theorem isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    IsIso (scalarSectionsBaseChangeMap φ f f' g w L.obj) := by
  let 𝒱 := Scheme.OrderedAffineCover.ofCompactSpace X
  let P := ModuleCat.extendScalars φ.hom
  let : PreservesFiniteLimits P :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  let A₀ := (augSc 𝒱 L.obj).map (relativeGlobalSections f)
  let A := A₀.map P
  let B := (augSc (inverseImageCover g 𝒱) ((Scheme.Modules.pullback g).obj L.obj)).map
    (relativeGlobalSections f')
  let : Mono (augmentation 𝒱 L.obj) := mono_augmentation L.obj
  let : Mono (augSc 𝒱 L.obj).f := mono_augmentation L.obj
  let : Mono A₀.f := (relativeGlobalSections f).map_mono (augmentation 𝒱 L.obj)
  let : Mono A.f := P.map_mono A₀.f
  let : Mono (augmentation (inverseImageCover g 𝒱)
      ((Scheme.Modules.pullback g).obj L.obj)) :=
    mono_augmentation ((Scheme.Modules.pullback g).obj L.obj)
  let : Mono B.f := (relativeGlobalSections f').map_mono
    (augmentation (inverseImageCover g 𝒱) ((Scheme.Modules.pullback g).obj L.obj))
  have hA₀ : A₀.Exact :=
    (exact_augSc (𝒰 := 𝒱) L.obj).map_of_mono_of_preservesKernel
      (relativeGlobalSections f) inferInstance inferInstance
  have hA : A.Exact :=
    hA₀.map_of_mono_of_preservesKernel P inferInstance inferInstance
  let t : A ⟶ B := {
    τ₁ := scalarSectionsBaseChangeMap φ f f' g w L.obj
    τ₂ := (scalarCechSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒱).f 0
    τ₃ := (scalarCechSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒱).f 1
    comm₁₂ := scalarSectionsBaseChangeMap_augmentation 𝒱 φ f f' g w L
    comm₂₃ := (scalarCechSectionsMap φ f f' g w
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app L.obj) 𝒱).comm 0 1 }
  let : IsIso t.τ₂ :=
    isIso_scalarCechSectionsMap_f_lineBundle_qcqs 𝒱 φ f f' g w L h hφ 0
  let : IsIso t.τ₃ :=
    isIso_scalarCechSectionsMap_f_lineBundle_qcqs 𝒱 φ f f' g w L h hφ 1
  exact isIso_left_of_leftExact t hA

/-- The canonical scalar sections isomorphism for a line bundle on a quasi-compact,
quasi-separated scheme under flat affine base change. -/
def scalarSectionsBaseChangeIso_lineBundle_qcqs [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj L.obj) ≅
      (relativeGlobalSections f').obj ((Scheme.Modules.pullback g).obj L.obj) := by
  let : IsIso (scalarSectionsBaseChangeMap φ f f' g w L.obj) :=
    isIso_scalarSectionsBaseChangeMap_lineBundle_qcqs φ f f' g w L h hφ
  exact asIso (scalarSectionsBaseChangeMap φ f f' g w L.obj)

@[simp]
lemma scalarSectionsBaseChangeIso_lineBundle_qcqs_hom [CompactSpace X]
    (h : IsPullback g f' f (Spec.map φ)) (hφ : φ.hom.Flat) :
    (scalarSectionsBaseChangeIso_lineBundle_qcqs φ f f' g w L h hφ).hom =
      scalarSectionsBaseChangeMap φ f f' g w L.obj := rfl

end Langlands.AlgebraicGeometry.Modules.CechResolution
