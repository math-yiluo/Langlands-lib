/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Direct image of an extension and its fibre torsor

Source: Stacks Project, Cohomology of Sheaves, Tags 02UV and 02FQ, and Sheaves of Modules,
Tag 01AX (blueprint: lem-sc-torsor-h1-ext-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

private theorem pullback_shortExact {C : Type*} [Category* C] [Abelian C]
    {F E Q A : C} (a : F ⟶ E) (p : E ⟶ Q) (w : a ≫ p = 0)
    (hS : (ShortComplex.mk a p w).ShortExact) (r : A ⟶ Q) :
    ∃ k : F ⟶ pullback p r, k ≫ pullback.fst _ _ = a ∧
      ∃ hk : k ≫ pullback.snd _ _ = 0,
        (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact := by
  let k : F ⟶ pullback p r := pullback.lift a 0 (by simp [w])
  have hk : k ≫ pullback.snd p r = 0 := by simp [k]
  refine ⟨k, by simp [k], hk, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  have : Mono k := mono_of_mono_fac (show k ≫ pullback.fst p r = a by simp [k])
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro B x hx
  obtain ⟨B', π, hπ, y, hy⟩ := hS.exact.exact_up_to_refinements
    (x ≫ pullback.fst p r) (by
      rw [Category.assoc, pullback.condition, reassoc_of% hx, zero_comp])
  refine ⟨B', π, hπ, y, ?_⟩
  apply pullback.hom_ext
  · simpa [k] using hy
  · simp [k, hx]

private theorem constant_restriction (Z X : TopCat.{u}) (f : Z ⟶ X) :
    ∃ r : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
        ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))),
      ∀ (U : Opens X) (n : ℤ),
        r.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op U) ⟨n⟩) =
          (toSheafify (Opens.grothendieckTopology Z)
            ((Functor.const (Opens Z)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
                (op ((Opens.map f).obj U)) ⟨n⟩ := by
  let Q := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
    ((constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
  let η : (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ Q.obj :=
    { app := fun U ↦ (toSheafify (Opens.grothendieckTopology Z)
        ((Functor.const (Opens Z)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app ((Opens.map f).op.obj U)
      naturality := fun U V g ↦ by
        simpa [Q, constantSheaf] using (toSheafify (Opens.grothendieckTopology Z)
          ((Functor.const (Opens Z)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).naturality ((Opens.map f).op.map g) }
  let r : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ Q :=
    ⟨sheafifyLift (Opens.grothendieckTopology X) η Q.property⟩
  refine ⟨r, ?_⟩
  intro U n
  have h := congrArg (fun α ↦ α.app (op U))
    (toSheafify_sheafifyLift (Opens.grothendieckTopology X) η Q.property)
  exact ConcreteCategory.congr_hom h ⟨n⟩

private theorem shortExact_closedEmbedding {Z X : TopCat.{u}} (f : Z ⟶ X)
    (hf : Topology.IsClosedEmbedding f)
    (S : ShortComplex (Z.Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).ShortExact := by
  apply (TopCat.shortExact_iff_stalkFunctor_map_shortExact _).mpr
  intro x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨z, rfl⟩ := hx
    let Φ := TopCat.Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor (X := X) AddCommGrpCat.{u} (f z)
    let Ψ := TopCat.Sheaf.forget AddCommGrpCat Z ⋙
      TopCat.Presheaf.stalkFunctor (X := Z) AddCommGrpCat.{u} z
    let c (F : Z.Sheaf AddCommGrpCat.{u}) :
        Φ.obj ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) ≅ Ψ.obj F := by
      have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat hf.isInducing F.obj z
      exact asIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat f F.obj z)
    have nat (F G : Z.Sheaf AddCommGrpCat.{u}) (a : F ⟶ G) :
        Φ.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map a) ≫ (c G).hom =
          (c F).hom ≫ Ψ.map a := by
      apply TopCat.Presheaf.stalk_hom_ext
      intro U hzU
      erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
      conv_rhs => rw [← Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ,
        TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    let e : (S.map (TopCat.Sheaf.pushforward AddCommGrpCat f)).map Φ ≅ S.map Ψ :=
      ShortComplex.isoMk (c S.X₁) (c S.X₂) (c S.X₃)
        (nat S.X₁ S.X₂ S.f).symm (nat S.X₂ S.X₃ S.g).symm
    exact ShortComplex.shortExact_of_iso e.symm (hS.map_of_exact Ψ)
  · have hz (F : Z.Sheaf AddCommGrpCat.{u}) :
        IsZero (TopCat.Presheaf.stalk
          ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj x) := by
      let P : TopCat.Presheaf AddCommGrpCat.{u} X :=
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).obj
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      suffices h : ∀ t : P.stalk x, t = 0 from ⟨fun a b ↦ (h a).trans (h b).symm⟩
      intro t
      obtain ⟨V, hV, hxV, s, rfl⟩ :=
        P.exists_le_germ_eq t (V := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩) hx
      have he : (Opens.map f).obj V = ⊥ := by
        ext z
        exact ⟨fun hz ↦ (hV hz) ⟨z, rfl⟩, fun hz ↦ False.elim hz⟩
      have hz := (F.isTerminalOfEqEmpty he).isZero
      have hs : s = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim _ _
      rw [hs]
      exact map_zero _
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂)) ?_ ?_
    · exact (hz S.X₁).mono _
    · exact (hz S.X₃).epi _

private theorem fibre_pullback_pushforward {Z X : TopCat.{u}} (f : Z ⟶ X)
    {F E Q : Z.Sheaf AddCommGrpCat.{u}} {A : X.Sheaf AddCommGrpCat.{u}}
    {a : F ⟶ E} {p : E ⟶ Q} {w : a ≫ p = 0}
    (hS : (ShortComplex.mk a p w).ShortExact)
    (r : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj Q)
    {k : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F ⟶
      pullback ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p) r}
    {hk : k ≫ pullback.snd _ _ = 0}
    (hP : (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact)
    (s : A.obj.obj (op ⊤)) (q : Q.obj.obj (op ⊤))
    (hr : ∀ U : Opens X,
      r.hom.app (op U) (A.obj.map (homOfLE le_top).op s) =
        Q.obj.map (homOfLE le_top).op q) :
    ∃ e : (lifts isTerminalTop hP s).sheaf ≅
        (TopCat.Sheaf.pushforward (Type u) f).obj (lifts isTerminalTop hS q).sheaf,
      ∀ (U : Opens X) (t : (lifts isTerminalTop hP s).sheaf.obj.obj (op U)),
        (e.hom.hom.app (op U) t).val =
          (pullback.fst ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p) r).hom.app
            (op U) t.val := by
  let p' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p
  let T := (lifts isTerminalTop hP s).sheaf
  let T' := (TopCat.Sheaf.pushforward (Type u) f).obj (lifts isTerminalTop hS q).sheaf
  let η : T.obj ⟶ T'.obj :=
    { app := fun U ↦ ↾fun t ↦ ⟨(pullback.fst p' r).hom.app U t.val, by
        have h : p'.hom.app U ((pullback.fst p' r).hom.app U t.val) =
            r.hom.app U ((pullback.snd p' r).hom.app U t.val) := by
          change ((pullback.fst p' r ≫ p').hom.app U) t.val =
            ((pullback.snd p' r ≫ r).hom.app U) t.val
          rw [pullback.condition]
        change p.hom.app ((Opens.map f).op.obj U)
            ((pullback.fst p' r).hom.app U t.val) = _
        change p'.hom.app U ((pullback.fst p' r).hom.app U t.val) = _
        rw [show p'.hom.app U ((pullback.fst p' r).hom.app U t.val) =
          r.hom.app U ((pullback.snd p' r).hom.app U t.val) from h]
        rw [lifts_val isTerminalTop hP t]
        exact hr U.unop⟩
      naturality := fun U V g ↦ by
        ext t
        apply Subtype.ext
        exact (ConcreteCategory.congr_hom ((pullback.fst p' r).hom.naturality g) t.val) }
  have bij (U : (Opens X)ᵒᵖ) : Function.Bijective (η.app U) := by
    let Φ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U ⋙ forget AddCommGrpCat.{u}
    have sq := Φ.map_isPullback (IsPullback.of_hasPullback p' r)
    constructor
    · intro t t' ht
      apply Subtype.ext
      apply Types.ext_of_isPullback sq
      · exact congrArg Subtype.val ht
      · exact t.property.trans t'.property.symm
    · intro t
      obtain ⟨x, hx, hy⟩ := Types.exists_of_isPullback sq t.val
        (A.obj.map (homOfLE le_top).op s) (t.property.trans (hr U.unop).symm)
      refine ⟨⟨x, hy⟩, ?_⟩
      exact Subtype.ext hx
  have : ∀ U, IsIso (η.app U) := fun U ↦
    (isIso_iff_bijective (η.app U)).mpr (bij U)
  have : IsIso η := NatIso.isIso_of_isIso_app η
  let e : T ≅ T' :=
    { hom := ⟨η⟩
      inv := ⟨inv η⟩
      hom_inv_id := by apply Sheaf.hom_ext; exact IsIso.hom_inv_id η
      inv_hom_id := by apply Sheaf.hom_ext; exact IsIso.inv_hom_id η }
  exact ⟨e, fun _ _ ↦ rfl⟩

private theorem constant_integer_one_restrict (Y : TopCat.{u}) (U : Opens Y) :
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))).obj.map (homOfLE le_top).op
        ((toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const (Opens Y)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩) =
      ((toSheafify (Opens.grothendieckTopology Y)
        ((Functor.const (Opens Y)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op U) ⟨1⟩) := by
  have h := (toSheafify (Opens.grothendieckTopology Y)
    ((Functor.const (Opens Y)ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).naturality (homOfLE (le_top : U ≤ ⊤)).op
  simpa [constantSheaf] using (ConcreteCategory.congr_hom h ⟨1⟩).symm

private theorem pullback_fibre_pushforward_equivariant {Z X : TopCat.{u}} (f : Z ⟶ X)
    {F E Q : Z.Sheaf AddCommGrpCat.{u}} {A : X.Sheaf AddCommGrpCat.{u}}
    {a : F ⟶ E} {p : E ⟶ Q} {w : a ≫ p = 0}
    (hS : (ShortComplex.mk a p w).ShortExact)
    (hD : ((ShortComplex.mk a p w).map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).ShortExact)
    (r : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj Q)
    (s : A.obj.obj (op ⊤)) (q : Q.obj.obj (op ⊤))
    (hr : ∀ U : Opens X,
      r.hom.app (op U) (A.obj.map (homOfLE le_top).op s) =
        Q.obj.map (homOfLE le_top).op q) :
    ∃ k : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F ⟶
        pullback ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p) r,
      k ≫ pullback.fst _ _ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map a ∧
      ∃ hk : k ≫ pullback.snd _ _ = 0,
        ∃ hP : (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact,
          ∃ e : (lifts isTerminalTop hP s).sheaf ≅
              (TopCat.Sheaf.pushforward (Type u) f).obj (lifts isTerminalTop hS q).sheaf,
            (∀ (U : Opens X) (t : (lifts isTerminalTop hP s).sheaf.obj.obj (op U)),
              (e.hom.hom.app (op U) t).val =
                (pullback.fst ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p) r).hom.app
                  (op U) t.val) ∧
            (∀ (U : Opens X)
                (g : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).obj.obj (op U))
                (t : (lifts isTerminalTop hP s).sheaf.obj.obj (op U)),
              e.hom.hom.app (op U) ((lifts isTerminalTop hP s).vadd (op U) g t) =
                (lifts isTerminalTop hS q).vadd (op ((Opens.map f).obj U)) g
                  (e.hom.hom.app (op U) t)) := by
  have (Y : TopCat.{u}) : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    inferInstance
  have (Y : TopCat.{u}) :
      (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  obtain ⟨k, hkfst, hk, hP⟩ := pullback_shortExact
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map a)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map p)
    (by simpa using ((ShortComplex.mk a p w).map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).zero) hD r
  refine ⟨k, hkfst, hk, hP, ?_⟩
  obtain ⟨e, he⟩ := fibre_pullback_pushforward f hS r hP s q hr
  refine ⟨e, he, ?_⟩
  intro U g t
  apply Subtype.ext
  rw [he]
  change (pullback.fst _ r).hom.app (op U)
      ((show (pullback _ r).obj.obj (op U) from t.val) + k.hom.app (op U) g) =
    (show E.obj.obj (op ((Opens.map f).obj U)) from
      (e.hom.hom.app (op U) t).val) + a.hom.app (op ((Opens.map f).obj U)) g
  erw [he U t]
  rw [map_add]
  congr 1
  change ((k ≫ pullback.fst _ r).hom.app (op U)) g = _
  rw [hkfst]
  rfl

/-- Direct image of an extension, pulled back along restriction of constant integer
sections, has fibre torsor canonically equal to the direct image of the original fibre.
The isomorphism is specified on sections by the first projection of the pullback, and it
commutes with translation by the direct-image group sheaf.
Source: Stacks Project, Tags 02UV, 02FQ and 01AX
(blueprint: lem-sc-torsor-h1-ext-pushforward).

Proof:
1. Identify the closed immersion with its closed image. Apply
`lem-sc-closed-immersion-pushforward-exact` to the original short exact sequence, obtaining
short exactness of its direct image. Restriction sends a constant integer to the same
integer on the inverse-image open. Pull back the sequence along this restriction map:
the kernel embeds by the unique map whose projections are the original inclusion and zero,
and epimorphy of the second projection follows from local lifting along the original
projection. This gives the asserted short exact pullback sequence.
2. On an open U, a lift of 1 in the pullback is a pair (e,1), where e is a section over
its inverse image and p(e)=1. First projection therefore identifies these lifts with
sections of the original fibre over the inverse-image open. These bijections commute with
restriction. They commute with translation because the kernel inclusion has first
projection equal to the pushed-forward inclusion. Consequently they form the canonical
isomorphism of torsors asserted in the statement (`lemma-cohomology-multiplicative-group--3`,
`lemma-uniform-bounds-pro-etale-affines` and `def-sc-topological-abelian-cohomology`). -/
theorem closedImmersion_extension_fibre_pushforward
    (Z X : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    (F E : Z.carrier.Sheaf AddCommGrpCat.{u})
    (a : F ⟶ E)
    (p : E ⟶ (constantSheaf (Opens.grothendieckTopology Z.carrier)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
    (w : a ≫ p = 0) (hS : (ShortComplex.mk a p w).ShortExact) :
    (ShortComplex.map (ShortComplex.mk a p w)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base)).ShortExact ∧
    ∃ r : (constantSheaf (Opens.grothendieckTopology X.carrier)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj
          ((constantSheaf (Opens.grothendieckTopology Z.carrier)
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))),
      (∀ (U : Opens X.carrier) (n : ℤ),
        r.hom.app (op U) ((toSheafify (Opens.grothendieckTopology X.carrier)
          ((Functor.const (Opens X.carrier)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op U) ⟨n⟩) =
          (toSheafify (Opens.grothendieckTopology Z.carrier)
            ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{u} ℤ)))).app
                (op ((Opens.map i.base).obj U)) ⟨n⟩) ∧
      ∃ k : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F ⟶
          pullback ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map p) r,
        k ≫ pullback.fst _ _ =
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map a ∧
        ∃ hk : k ≫ pullback.snd _ _ = 0,
          ∃ hP : (ShortComplex.mk k (pullback.snd _ _) hk).ShortExact,
            ∃ e : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                ((toSheafify (Opens.grothendieckTopology X.carrier)
                  ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                    (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf ≅
                (TopCat.Sheaf.pushforward (Type u) i.base).obj
                  (lifts (isTerminalTop : IsTerminal (⊤ : Opens Z.carrier)) hS
                    ((toSheafify (Opens.grothendieckTopology Z.carrier)
                      ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf,
              (∀ (U : Opens X.carrier)
                  (t : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf.obj.obj (op U)),
                (e.hom.hom.app (op U) t).val = (pullback.fst
                  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map p) r).hom.app
                    (op U) t.val) ∧
              (∀ (U : Opens X.carrier)
                  (g : ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj F).obj.obj
                    (op U))
                  (t : (lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).sheaf.obj.obj (op U)),
                e.hom.hom.app (op U)
                  ((lifts (isTerminalTop : IsTerminal (⊤ : Opens X.carrier)) hP
                    ((toSheafify (Opens.grothendieckTopology X.carrier)
                      ((Functor.const (Opens X.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).vadd (op U) g t) =
                  (lifts (isTerminalTop : IsTerminal (⊤ : Opens Z.carrier)) hS
                    ((toSheafify (Opens.grothendieckTopology Z.carrier)
                      ((Functor.const (Opens Z.carrier)ᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩)).vadd
                          (op ((Opens.map i.base).obj U)) g (e.hom.hom.app (op U) t)) := by
  -- Reuse sheafification instances while specializing the general pullback construction.
  have (Y : TopCat.{u}) : HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    inferInstance
  have (Y : TopCat.{u}) :
      (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have hD := shortExact_closedEmbedding i.base i.isClosedEmbedding
    (ShortComplex.mk a p w) hS
  refine ⟨hD, ?_⟩
  obtain ⟨r, hr⟩ := constant_restriction Z.carrier X.carrier i.base
  refine ⟨r, hr, ?_⟩
  refine pullback_fibre_pushforward_equivariant i.base hS hD r _ _ ?_
  intro U
  erw [constant_integer_one_restrict X.carrier U, hr U 1,
    constant_integer_one_restrict Z.carrier ((Opens.map i.base).obj U)]

end CategoryTheory.Sheaf.Torsor
