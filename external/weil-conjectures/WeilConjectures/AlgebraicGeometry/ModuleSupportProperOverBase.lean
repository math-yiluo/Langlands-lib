/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport

/-! # Support of a finite type module proper over a base

Source: Stacks Project, Cohomology of Schemes, Lemma 0CYS, together with
Morphisms Lemmas 056J, 05JU, Definition 05JV, and Lemma 01QY
(blueprint: lem-weil-pbc-module-support-proper-over-base).

## Main statements

* `module_support_proper_over_base` states closedness of the support and the
  characterization of proper support by a proper closed subscheme annihilating
  the module.
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent finite type module, the support is closed, and it is proper
over the base exactly when the module is annihilated by the ideal of a proper closed
subscheme, equivalently a finite type quasi-coherent pushforward from that subscheme.
The last conjunct permits taking the scheme-theoretic support: its ideal agrees on
all affine opens with the annihilator, and its underlying set is exactly the support.
Source: Stacks Project, Cohomology of Schemes, Lemma 0CYS, and Morphisms Lemmas
056J, 05JU, Definition 05JV, and Lemma 01QY
(blueprint: lem-weil-pbc-module-support-proper-over-base).
Proof, following the node's five steps:
1. By lem-weil-pbc-finite-type-module-support-closed (056J), support is closed;
on affine opens it is the zero locus of the annihilator of the section module.
2. By lem-weil-pbc-scheme-theoretic-support (05JU/05JV), the annihilator is a
quasi-coherent ideal sheaf. Its closed subscheme has underlying set exactly the
support and its ideal kills F. This supplies the final conjunct's chosen subscheme.
3. If support is proper, lem-weil-pbc-closed-subset-proper-over-base-properties (1)
makes every closed subscheme structure on it proper, including this chosen one.
4. Conversely, if the ideal of a proper closed subscheme kills F, support lies in
its image: on the complementary open the ideal contains 1, so all sections, and
hence all stalks, vanish. That image is proper by the same properties lemma (1),
and its closed subset Supp(F) is proper by part (2) of that lemma (0CYN).
5. By lem-weil-pbc-closed-immersion-pushforward-annihilated (01QY), annihilation
identifies F with the pushforward of its tensor pullback (def-pc-module-pullback),
which is quasi-coherent and of finite type. Conversely the ideal kills every
pushforward and this passes along the module isomorphism. Apply this also to the
scheme-theoretic support selected in step 2.
-/
theorem module_support_proper_over_base {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (∃ Z : TopologicalSpace.Closeds X,
      (Z : Set X) = {x : X | ¬ Subsingleton (F.presheaf.stalk x)}) ∧
      (HasSupportProperOver f F ↔
        ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
          IsProper (i ≫ f) ∧
            (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
              ∀ s : Γ(F, V), a • s = 0) ∧
            ∃ (G : Z.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
              Nonempty (F ≅ (pushforward i).obj G)) ∧
      (∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i),
        (∀ U : X.affineOpens,
          i.ker.ideal U = Module.annihilator Γ(X, U) Γ(F, U)) ∧
          Set.range i = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
          (∀ (V : X.Opens) (a : Γ(X, V)), a ∈ i.ker.idealOfOpens V →
            ∀ s : Γ(F, V), a • s = 0) ∧
          (∃ (G : Z.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
            Nonempty (F ≅ (pushforward i).obj G)) ∧
          (HasSupportProperOver f F ↔ IsProper (i ≫ f))) := by
  classical
  let C : TopologicalSpace.Closeds X :=
    ⟨{x : X | ¬ Subsingleton (F.presheaf.stalk x)},
      (finite_type_module_support_closed X F).2.2.2⟩
  obtain ⟨I, hI, hi, hker, _, _, hrange, hkill, _⟩ := schemeTheoreticSupport X F
  have : IsClosedImmersion I.subschemeι := hi
  have hann : ∀ (V : X.Opens) (a : Γ(X, V)),
      a ∈ I.subschemeι.ker.idealOfOpens V → ∀ s : Γ(F, V), a • s = 0 := by
    intro V a ha s
    rw [hker] at ha
    exact hkill V ⟨a, ha⟩ s
  have hpush : ∃ (G : I.subscheme.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
      Nonempty (F ≅ (pushforward I.subschemeι).obj G) := by
    obtain ⟨hq, he, hf⟩ :=
      (closedImmersion_pushforward_annihilated I.subschemeι).2 F hann
    have := hq
    have := hf (inferInstance : F.IsFiniteType)
    have := he
    exact ⟨(tensorPullback I.subschemeι).obj F, inferInstance, inferInstance,
      ⟨asIso ((Classical.choose
        (exists_tensorPullbackAdjunction I.subschemeι)).unit.app F)⟩⟩
  have hproper : HasSupportProperOver f F ↔ IsProper (I.subschemeι ≫ f) := by
    constructor
    · rintro ⟨D, hD, hp⟩
      exact (closed_subset_proper_over_base_properties f D).2.1.mp hp
        I.subscheme I.subschemeι (hrange.trans hD.symm)
    · intro hp
      exact ⟨C, rfl, (closed_subset_proper_over_base_properties f C).1.mpr
        ⟨I.subscheme, I.subschemeι, inferInstance, hrange, hp⟩⟩
  refine ⟨⟨C, rfl⟩, ⟨?_, ?_⟩, I.subscheme, I.subschemeι, inferInstance,
    ?_, hrange, hann, hpush, hproper⟩
  · intro hp
    exact ⟨I.subscheme, I.subschemeι, inferInstance, hproper.mp hp, hann, hpush⟩
  · rintro ⟨Z, i, hi, hp, _, G, hq, hf, ⟨e⟩⟩
    have : IsClosedImmersion i := hi
    let D : TopologicalSpace.Closeds X :=
      ⟨Set.range i.base, i.isClosedEmbedding.isClosed_range⟩
    have hCD : C ≤ D := by
      intro x hx
      by_contra hn
      have hz := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).1 x hn
      let T := SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          TopCat.Presheaf.stalkFunctor Ab.{u} x
      have heq := ConcreteCategory.bijective_of_isIso (T.map e.hom)
      have : Subsingleton (F.presheaf.stalk x) :=
        ⟨fun a b ↦ heq.1 (hz.elim _ _)⟩
      exact hx this
    have hD : IsClosedSubsetProperOver f D :=
      (closed_subset_proper_over_base_properties f D).1.mpr
        ⟨Z, i, inferInstance, rfl, hp⟩
    exact ⟨C, rfl, (closed_subset_proper_over_base_properties f D).2.2.1 C hCD hD⟩
  · intro U
    rw [hker]
    exact hI U

end AlgebraicGeometry.Scheme.Modules
