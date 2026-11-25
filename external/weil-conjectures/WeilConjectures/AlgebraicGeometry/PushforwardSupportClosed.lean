/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Closed support of a proper coherent pushforward

Source: Stacks Project, Theorem 088E, support of H paragraph, and Proposition 02O5.
The assertion isolates closedness and containment; properness over a further base
is proved separately in `ChowAlgebraizationSupport`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The support of a pushforward is closed and is contained in the image of the support.
Source: Stacks Project, Tag 088E, support paragraph (the closedness and stalk argument).
(blueprint: new-chow-pushforward-support-closed)

Proof: A proper morphism to the Noetherian Z is of finite type, hence Y is
Noetherian too. Tag 02O5 implies that q_*F is coherent. On a Noetherian scheme,
a coherent module is quasi-coherent of finite type (Tag 01XZ), so its support is
closed (Tag 056J). Give that support its closed-set structure D.
Because q is proper it is a closed map; thus q(C) is closed. For x outside q(C),
the open neighbourhood V = Z \ q(C) has inverse image disjoint from C. Every
stalk of F on q^{-1}(V) is zero by hC. Given two sections over any open inside
q^{-1}(V), equality of their germs supplies a neighbourhood of each point on
which they agree. Sheaf separatedness then makes the sections equal, including
on the empty open. Therefore q_*F has only one section over every open inside V.
Every germ at x is represented on an open neighbourhood; intersect that open
with V to conclude that the stalk of q_*F at x is zero. Taking the contrapositive
gives D ⊆ q(C). The construction also covers F = 0 and empty Y or Z.
-/
theorem pushforward_support_closed_subset
    {Z Y : Scheme.{u}} [IsNoetherian Z]
    (q : Y ⟶ Z) [IsProper q] (F : CoherentModules Y)
    (C : TopologicalSpace.Closeds Y)
    (hC : (C : Set Y) = {x : Y | ¬ Subsingleton (F.obj.presheaf.stalk x)}) :
    ∃ D : TopologicalSpace.Closeds Z,
      (D : Set Z) =
        {x : Z | ¬ Subsingleton (((Scheme.Modules.pushforward q).obj F.obj).presheaf.stalk x)} ∧
      (D : Set Z) ⊆ q '' (C : Set Y) := by
  classical
  have := Scheme.Modules.isGrothendieckAbelian Y
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hq := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F.obj).mp
    F.property
  have : F.obj.IsQuasicoherent := hq.1
  have finitePresentation
      {C : Type u} [SmallCategory C] [Limits.HasBinaryProducts C]
      [∀ U : C, Limits.HasBinaryProducts (Over U)]
      {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
      [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
      [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
      (F : SheafOfModules.{u} R) (hfin : F.IsFiniteType)
      (hker : ∀ (U : C) (n : ℕ)
        (f : SheafOfModules.free (R := R.over U) (ULift.{u} (Fin n)) ⟶ F.over U),
        (Limits.kernel f).IsFiniteType) : F.IsFinitePresentation := by
    classical
    have : F.IsFiniteType := hfin
    obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
    have hfp (i : q.I) :
        SheafOfModules.IsFinitePresentation (R := R.over (q.X i))
          (F.over (q.X i)) := by
      have := hq.isFiniteType i
      let _ := Fintype.ofFinite (q.generators i).I
      let n := Fintype.card (q.generators i).I
      let e := (SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
        ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
      let f := e.hom ≫ (q.generators i).π
      have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
      let G := SheafOfModules.GeneratingSections.ofEpiFree f
      have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
      have : (Limits.kernel G.π).IsFiniteType := by
        simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
          using hker (q.X i) n f
      exact Scheme.Modules.isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      F q.I q.X q.coversTop hfp
  have : F.obj.IsFinitePresentation := finitePresentation F.obj F.property.1 F.property.2
  have hqc := Scheme.Modules.isQuasicoherent_higherDirectImage q F.obj 0
  have hfp := Scheme.Modules.isFinitePresentation_higherDirectImage q F.obj 0
  let e := ((Scheme.Modules.pushforward q).rightDerivedZeroIsoSelf).app F.obj
  have : ((Scheme.Modules.pushforward q).obj F.obj).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e hqc
  have : ((Scheme.Modules.pushforward q).obj F.obj).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation Z.ringCatSheaf).prop_of_iso e hfp
  let D : TopologicalSpace.Closeds Z := ⟨_, (Scheme.Modules.finite_type_module_support_closed Z
    ((Scheme.Modules.pushforward q).obj F.obj)).2.2.2⟩
  refine ⟨D, rfl, ?_⟩
  intro x hx
  by_contra hnot
  let V : TopologicalSpace.Opens Z :=
    ⟨(q '' (C : Set Y))ᶜ, (q.isClosedMap _ C.isClosed).isOpen_compl⟩
  have hxV : x ∈ V := hnot
  let P := ((Scheme.Modules.pushforward q).obj F.obj).presheaf
  have trivial (U : TopologicalSpace.Opens Z) (hU : U ≤ V) :
      Subsingleton (P.obj (Opposite.op U)) := by
    change Subsingleton
      (F.obj.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map q.base).obj U)))
    refine ⟨fun s t ↦ TopCat.Presheaf.section_ext ⟨F.obj.presheaf, F.obj.isSheaf⟩ _ s t
      (fun y hy ↦ ?_)⟩
    have hyC : y ∉ (C : Set Y) := fun h ↦ (hU hy) ⟨y, h, rfl⟩
    have hs : Subsingleton (F.obj.presheaf.stalk y) := by
      by_contra hn
      exact hyC (by rw [hC]; exact hn)
    exact hs.elim _ _
  apply hx
  refine ⟨?_⟩
  intro a b
  obtain ⟨U, hUV, hxU, s, rfl⟩ := P.exists_le_germ_eq a hxV
  obtain ⟨W, hWV, hxW, t, rfl⟩ := P.exists_le_germ_eq b hxV
  let Q := U ⊓ W
  have hxQ : x ∈ Q := ⟨hxU, hxW⟩
  have := trivial Q (inf_le_left.trans hUV)
  have heq : P.map (homOfLE (inf_le_left : Q ≤ U)).op s =
      P.map (homOfLE (inf_le_right : Q ≤ W)).op t := Subsingleton.elim _ _
  rw [← P.germ_res_apply (homOfLE (inf_le_left : Q ≤ U)) x hxQ s,
    ← P.germ_res_apply (homOfLE (inf_le_right : Q ≤ W)) x hxQ t, heq]

end AlgebraicGeometry
