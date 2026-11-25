/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenExistence
import WeilConjectures.AlgebraicGeometry.EtaleCechSectionsConnectedGeometricFibre
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt

/-! # Compatibility of sections on connected geometric fibres

Source: Stacks Project, Etale Cohomology, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-connected-fibres-section-compatible).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private abbrev idEtale (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private noncomputable abbrev setUnit {X Y : Scheme.{u}} (e : Y ⟶ X) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit

private noncomputable def resGlobal {X Y : Scheme.{u}} (e : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    G.obj.obj (op (idEtale X)) ⟶
      ((Scheme.etaleSetPullback e).obj G).obj.obj (op (idEtale Y)) :=
  ((setUnit e).app G).hom.app (op (idEtale X)) ≫
    ((Scheme.etaleSetPullback e).obj G).obj.map
      (MorphismProperty.Over.homMk
        (pullback.lift e (𝟙 Y)
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
        idEtale Y ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ e).obj (idEtale X)).op

private theorem global_eq_of_identity_pullback (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (a b : G.obj.obj (op (idEtale X)))
    (hab : (resGlobal (𝟙 X) G) a = (resGlobal (𝟙 X) G) b) : a = b := by
  apply etaleSetSection_ext_of_geometric_germs X G (idEtale X)
  intro Ω _ _ x z
  have hz : z = Over.homMk x (Category.comp_id x) := by
    apply Over.OverMorphism.ext
    simpa using Over.w z
  rw [hz]
  obtain ⟨c, _, hunit, _⟩ := etaleSetInverseImageStalkGerm X X (𝟙 X) G Ω x
  let j : idEtale X ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 X)).obj (idEtale X) :=
    MorphismProperty.Over.homMk
      (pullback.lift (𝟙 X) (𝟙 X)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)
  have hp : (Scheme.pointSmallEtale x).fiber.map j
      (Over.homMk x (Category.comp_id x)) =
      Over.homMk (pullback.lift x x (by simp)) (pullback.lift_snd _ _ _) := by
    apply Over.OverMorphism.ext
    change x ≫ pullback.lift (𝟙 X) (𝟙 X) _ = pullback.lift x x _
    apply pullback.hom_ext <;> simp
  have heq (t : G.obj.obj (op (idEtale X))) :
      c ((Scheme.pointSmallEtale x).toPresheafFiber (idEtale X)
        (Over.homMk x (Category.comp_id x)) ((Scheme.etaleSetPullback (𝟙 X)).obj G).obj
          ((resGlobal (𝟙 X) G) t)) =
      (Scheme.pointSmallEtale (x ≫ 𝟙 X)).toPresheafFiber (idEtale X)
        (Over.homMk x (by simp)) G.obj t := by
    have hn := ConcreteCategory.congr_hom
      ((Scheme.pointSmallEtale x).toPresheafFiber_w j
        (Over.homMk x (Category.comp_id x)) ((Scheme.etaleSetPullback (𝟙 X)).obj G).obj)
      (((setUnit (𝟙 X)).app G).hom.app (op (idEtale X)) t)
    simp only [types_comp_apply] at hn
    rw [hp] at hn
    exact (congrArg c hn).trans (hunit (idEtale X) (Over.homMk x (by simp)) t)
  have h := congrArg
    (fun t ↦ c ((Scheme.pointSmallEtale x).toPresheafFiber (idEtale X)
      (Over.homMk x (Category.comp_id x)) ((Scheme.etaleSetPullback (𝟙 X)).obj G).obj t)) hab
  rw [heq a, heq b] at h
  have transport (y : Spec (.of Ω) ⟶ X) (hy : x ≫ 𝟙 X = y) :
      (Scheme.pointSmallEtale y).toPresheafFiber (idEtale X)
        (Over.homMk x (by simpa using hy)) G.obj a =
      (Scheme.pointSmallEtale y).toPresheafFiber (idEtale X)
        (Over.homMk x (by simpa using hy)) G.obj b := by
    subst y
    exact h
  exact transport x (Category.comp_id x)

private theorem global_eq_of_jointly_surjective
    {X : Scheme.{u}} {J : Type u} (Y : J → Scheme.{u}) (e : ∀ j, Y j ⟶ X)
    (hcover : ∀ x : X, ∃ j, x ∈ Set.range (e j))
    (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (a b : G.obj.obj (op (idEtale X)))
    (hab : ∀ j, (resGlobal (e j) G) a = (resGlobal (e j) G) b) : a = b := by
  obtain ⟨W, hW⟩ := exists_etaleSections_equal_open X G (idEtale X) a b
  have hfac (j : J) : ∃ k : Y j ⟶ W.toScheme, k ≫ W.ι = e j := by
    apply (hW (Y j) (e j)).mpr
    change (resGlobal (e j ≫ 𝟙 X) G) a = (resGlobal (e j ≫ 𝟙 X) G) b
    have transport (e' : Y j ⟶ X) (he : e' = e j) :
        (resGlobal (e') G) a = (resGlobal (e') G) b := by
      subst e'
      exact hab j
    exact transport _ (Category.comp_id _)
  have htop : W = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨j, y, rfl⟩ := hcover x
    obtain ⟨k, hk⟩ := hfac j
    have hx := congrArg (fun t : Y j ⟶ X ↦ t y) hk
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hx
    rw [← hx]
    exact (k y).property
  have hid := (hW X (𝟙 X)).mp
    ⟨IsOpenImmersion.lift W.ι (𝟙 X) (by simp [Scheme.Opens.range_ι, htop]),
      IsOpenImmersion.lift_fac W.ι (𝟙 X) _⟩
  apply global_eq_of_identity_pullback X G a b
  change (resGlobal (𝟙 X ≫ 𝟙 X) G) a = (resGlobal (𝟙 X ≫ 𝟙 X) G) b at hid
  have transport (e' : X ⟶ X) (he : e' = 𝟙 X) :
      (resGlobal e' G) a = (resGlobal e' G) b →
        (resGlobal (𝟙 X) G) a = (resGlobal (𝟙 X) G) b := by
    subst e'
    exact id
  exact transport _ (Category.comp_id _) hid

/-- Every section of an etale inverse image along a morphism with connected
geometric fibres has equal pullbacks along the two Cech projections. The comparisons
are the unit-compatible composition comparisons, evaluated at the terminal etale
object. Flatness and quasi-compactness are not required for this assertion.

Source: Stacks Project, Etale Cohomology, Tag 0A3H, final paragraph.
(blueprint: lem-weil-pbc-etale-connected-fibres-section-compatible).

Proof:
1. For each point s of S choose the canonical geometric point q from the algebraic
   closure of its residue field. The maps D ×_S Spec Ω → D jointly cover D:
   the pullback range formula and the residue-field point show that the fibre
   indexed by g(x) contains each x in D, where g = pr₁ ≫ f.
2. Apply etaleSet_cech_sections_agree_on_connected_geometric_fibre at each q.
   Its connectedness hypothesis is exactly hconn s. Thus the restrictions of the
   two displayed sections agree on every member of this jointly surjective family.
3. The agreement-open universal property factors all these maps through an open
   W of D. Joint surjectivity implies W = top, hence the two sections have equal
   identity pullbacks. Inverse-image stalk comparison and germ naturality recover
   equality of their original germs; geometric-germ extensionality gives equality
   of the sections. The argument also applies to empty D. -/
theorem etaleSet_section_compatible_of_connected_geometricFibres
    {S T : Scheme.{u}} (f : T ⟶ S)
    (hconn : ∀ s : S, ConnectedSpace
      (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}))
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (a : ((Scheme.etaleSetPullback f).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 T)))) :
      ((Classical.choose etaleSetInverseImageCompositionUnits.2.2
          S T (pullback f f) f (pullback.fst f f)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (pullback f f))))
        (((Scheme.etaleSetPullback (pullback.fst f f)).obj
            ((Scheme.etaleSetPullback f).obj F)).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (pullback.fst f f) (𝟙 (pullback f f))
              ((Category.comp_id _).trans (Category.id_comp _).symm))
            (by simp) :
            Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)).obj
                (Scheme.Etale.mk (𝟙 T))).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ (pullback.fst f f)) _
            (T.smallGrothendieckTopology @Etale)
            ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback f).obj F)).hom.app
            (op (Scheme.Etale.mk (𝟙 T))) a)) =
        Eq.mp (congrArg (fun k : pullback f f ⟶ S ↦
          ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op (Scheme.Etale.mk (𝟙 (pullback f f)))))
          (pullback.condition (f := f) (g := f)).symm)
        (((Classical.choose etaleSetInverseImageCompositionUnits.2.2
            S T (pullback f f) f (pullback.snd f f)).hom.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 (pullback f f))))
          (((Scheme.etaleSetPullback (pullback.snd f f)).obj
              ((Scheme.etaleSetPullback f).obj F)).obj.map
            (MorphismProperty.Over.homMk
              (pullback.lift (pullback.snd f f) (𝟙 (pullback f f))
                ((Category.comp_id _).trans (Category.id_comp _).symm))
              (by simp) :
              Scheme.Etale.mk (𝟙 (pullback f f)) ⟶
                (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)).obj
                  (Scheme.Etale.mk (𝟙 T))).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (pullback.snd f f)) _
              (T.smallGrothendieckTopology @Etale)
              ((pullback f f).smallGrothendieckTopology @Etale)).unit.app
                ((Scheme.etaleSetPullback f).obj F)).hom.app
              (op (Scheme.Etale.mk (𝟙 T))) a))) := by
  classical
  let q (s : S) : Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
        S.fromSpecResidueField s
  let g := pullback.fst f f ≫ f
  have hcover : ∀ x : (pullback f f : Scheme.{u}),
      ∃ s : S, x ∈ Set.range (pullback.fst g (q s)) := by
    intro x
    refine ⟨g x, ?_⟩
    rw [Scheme.Pullback.range_fst]
    refine ⟨default, ?_⟩
    exact S.fromSpecResidueField_apply (g x) _
  apply global_eq_of_jointly_surjective
    (fun s : S ↦ pullback g (q s)) (fun s ↦ pullback.fst g (q s)) hcover
  intro s
  have : ConnectedSpace (pullback f (q s) : Scheme.{u}) := hconn s
  exact etaleSet_cech_sections_agree_on_connected_geometric_fibre f
    (AlgebraicClosure (S.residueField s)) (q s) F a

end AlgebraicGeometry
