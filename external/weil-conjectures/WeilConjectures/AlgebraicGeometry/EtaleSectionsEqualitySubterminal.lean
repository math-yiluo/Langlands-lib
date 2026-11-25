/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm

/-! # The subterminal sheaf of agreement of two étale sections

Source: Stacks Project, Étale Cohomology, Tag 09XM, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def toIdentity (T : Scheme.{u}) (U : T.Etale) : U ⟶ Scheme.Etale.mk (𝟙 T) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom)
private theorem comp_toIdentity (T : Scheme.{u}) {U V : T.Etale} (f : U ⟶ V) :
    f ≫ toIdentity T V = toIdentity T U := by
  apply MorphismProperty.Over.Hom.ext
  exact MorphismProperty.Over.w f

private theorem global_agreement_subterminal (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (p q : G.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    ∃ H : Sheaf T.smallEtaleTopology (Type (u + 1)), Mono (terminal.from H) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
        Nonempty ((Scheme.pointSmallEtale x).sheafFiber.obj H) ↔
        (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
          (Over.homMk x (Category.comp_id x)) G.obj p =
        (Scheme.pointSmallEtale x).toPresheafFiber (Scheme.Etale.mk (𝟙 T))
          (Over.homMk x (Category.comp_id x)) G.obj q := by
  let K : T.Etaleᵒᵖ ⥤ Type (u + 1) := (Functor.const _).obj PUnit
  let A : Subfunctor K :=
    { obj := fun U ↦ { z | G.obj.map (toIdentity T U.unop).op p =
                          G.obj.map (toIdentity T U.unop).op q }
      map := by
        intro U V f z hz
        change G.obj.map (toIdentity T V.unop).op p =
          G.obj.map (toIdentity T V.unop).op q
        rw [← comp_toIdentity T f.unop, op_comp, G.obj.map_comp]
        exact congrArg (G.obj.map f) hz }
  have hK : Presieve.IsSheaf T.smallEtaleTopology K :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit)
  have hA : Presheaf.IsSheaf T.smallEtaleTopology A.toFunctor := by
    apply (isSheaf_iff_isSheaf_of_type _ _).mpr
    apply (A.isSheaf_iff hK).mpr
    intro U z hz
    change G.obj.map (toIdentity T U.unop).op p =
      G.obj.map (toIdentity T U.unop).op q
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated _ hz).ext
    intro V f hf
    change G.obj.map (toIdentity T V).op p = G.obj.map (toIdentity T V).op q at hf
    simpa only [← Functor.map_comp_apply, ← op_comp, comp_toIdentity] using hf
  let H : Sheaf T.smallEtaleTopology (Type (u + 1)) := ⟨A.toFunctor, hA⟩
  refine ⟨H, ?_, ?_⟩
  · rw [Sheaf.Hom.mono_iff_presheaf_mono]
    rw [NatTrans.mono_iff_mono_app]
    intro U
    apply ConcreteCategory.mono_of_injective
    intro z z' _
    apply Subtype.ext
    exact @Subsingleton.elim (PUnit : Type (u + 1)) inferInstance z.val z'.val
  · intro Ω _ _ x
    constructor
    · rintro ⟨z⟩
      obtain ⟨U, y, a, ha⟩ := (Scheme.pointSmallEtale x).toPresheafFiber_jointly_surjective
        (P := H.obj) z
      have hay : (Scheme.pointSmallEtale x).fiber.map (toIdentity T U) y =
          Over.homMk x (Category.comp_id x) := by
        apply Over.OverMorphism.ext
        exact Over.w y
      have hp := (Scheme.pointSmallEtale x).toPresheafFiber_w_apply
        (toIdentity T U) y G.obj p
      have hq := (Scheme.pointSmallEtale x).toPresheafFiber_w_apply
        (toIdentity T U) y G.obj q
      rw [hay] at hp hq
      exact hp.symm.trans ((congrArg
        ((Scheme.pointSmallEtale x).toPresheafFiber U y G.obj) a.property).trans hq)
    · intro h
      obtain ⟨U, f, y, hy, hf⟩ :=
        ((Scheme.pointSmallEtale x).toPresheafFiber_eq_iff' (P := G.obj)
          (Scheme.Etale.mk (𝟙 T)) _ p q).mp h
      have he : f = toIdentity T U := by
        apply MorphismProperty.Over.Hom.ext
        change f.left = U.hom
        exact (Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f)
      rw [he] at hf
      exact ⟨(Scheme.pointSmallEtale x).toPresheafFiber U y H.obj ⟨PUnit.unit, hf⟩⟩

/-- The agreement of two sections gives a subterminal sheaf on the small étale site of
`V.left`. Its stalk is inhabited precisely when the original sections have equal germs.
Source: Stacks Project, Étale Cohomology, Tag 09XM, first paragraph of the proof;
Tag 03Q1 for the identification with the original sheaf's germs.
(blueprint: lem-weil-pbc-etale-sections-equality-subterminal).

Proof:
Restrict `F` to the small étale site of `V.left`. For an étale `U → V.left`, define
`H(U)` to be a singleton when the restrictions of `s` and `t` along `U → V.left → S`
are equal, and empty otherwise. Equality is preserved by restriction, so these sets
form a presheaf. Sections on a covering family agree automatically on overlaps.
They give equality of the two restricted sections on the cover, hence on `U` by
separatedness of the restricted sheaf. Thus they glue to the unique element of `H(U)`.
Every section set is a subsingleton, making the unique map to the terminal sheaf mono.
At a geometric point `x`, a germ of `H` is represented by an agreement neighbourhood,
so it implies equality of the germs of the two sections. Conversely, equality of germs
in the filtered colimit of pointed étale neighbourhoods is witnessed on a common
neighbourhood, which then has a section of `H`. The inverse-image stalk identification
of Tag 03Q1, with its unit formula, identifies these germs of the restricted sheaf with
those of `F` at `x ≫ V.hom`, with pointed lift `x` to `V`. -/
theorem exists_etaleSections_equality_subterminal (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) (s t : F.obj.obj (op V)) :
    ∃ H : Sheaf V.left.smallEtaleTopology (Type (u + 1)),
      Mono (terminal.from H) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ V.left),
        Nonempty ((Scheme.pointSmallEtale x).sheafFiber.obj H) ↔
          (Scheme.pointSmallEtale (x ≫ V.hom)).toPresheafFiber V
            (Over.homMk x rfl) F.obj s =
          (Scheme.pointSmallEtale (x ≫ V.hom)).toPresheafFiber V
            (Over.homMk x rfl) F.obj t := by
  let G := (Scheme.etaleSetPullback V.hom).obj F
  let I : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let k : I ⟶ (MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) rfl)
      (pullback.lift_snd (𝟙 V.left) (𝟙 V.left) rfl)
  let η : F.obj.obj (op V) ⟶
      G.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ V.hom).obj V)) :=
    ((@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _
      (MorphismProperty.Over.pullback @Etale ⊤ V.hom) (Type (u + 1)) _
      (S.smallGrothendieckTopology @Etale) (V.left.smallGrothendieckTopology @Etale)
      (Etale.isContinuous_overPullback V.hom) _ _).unit.app F).hom.app (op V)
  let r : F.obj.obj (op V) → G.obj.obj (op I) := fun z ↦ G.obj.map k.op (η z)
  obtain ⟨H, hmono, hgerms⟩ := global_agreement_subterminal V.left G (r s) (r t)
  refine ⟨H, hmono, ?_⟩
  intro Ω _ _ x
  rw [hgerms Ω x]
  obtain ⟨c, hc, hunit, _⟩ := etaleSetInverseImageStalkGerm S V.left V.hom F Ω x
  have hp : (Scheme.pointSmallEtale x).fiber.map k (Over.homMk x (Category.comp_id x)) =
      Over.homMk (pullback.lift x x rfl) (pullback.lift_snd x x rfl) := by
    apply Over.OverMorphism.ext
    change x ≫ pullback.lift (𝟙 V.left) (𝟙 V.left) _ = pullback.lift x x _
    apply pullback.hom_ext <;> simp
  have heq (z : F.obj.obj (op V)) :
      c ((Scheme.pointSmallEtale x).toPresheafFiber I
        (Over.homMk x (Category.comp_id x)) G.obj (r z)) =
      (Scheme.pointSmallEtale (x ≫ V.hom)).toPresheafFiber V
        (Over.homMk x rfl) F.obj z := by
    have hn := ConcreteCategory.congr_hom
      ((Scheme.pointSmallEtale x).toPresheafFiber_w k
        (Over.homMk x (Category.comp_id x)) G.obj) (η z)
    simp only [types_comp_apply] at hn
    rw [hp] at hn
    rw [show (Scheme.pointSmallEtale x).toPresheafFiber I
        (Over.homMk x (Category.comp_id x)) G.obj (r z) = _ from hn]
    exact hunit V (Over.homMk x rfl) z
  rw [← hc.1.eq_iff, heq s, heq t]

end AlgebraicGeometry
