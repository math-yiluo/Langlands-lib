/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Construction of the open support of a subterminal étale sheaf -/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Section factorization property for an open. -/
def etaleSubsheafFactorization (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v))) (W : S.Opens) : Prop :=
  ∀ U : S.Etale,
    (Nonempty (Unique (H.obj.obj (op U))) ↔
      ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) ∧
    ((¬ ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom) →
      IsEmpty (H.obj.obj (op U)))

private theorem section_subsingleton (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] (U : S.Etale) :
    Subsingleton (H.obj.obj (op U)) := by
  let E := sheafToPresheaf S.smallEtaleTopology (Type (max u v)) ⋙
    (CategoryTheory.evaluation S.Etaleᵒᵖ (Type (max u v))).obj (op U)
  have ht := IsTerminal.isTerminalObj E _
    (terminalIsTerminal (C := Sheaf S.smallEtaleTopology (Type (max u v))))
  let : Unique (E.obj (⊤_ _)) := Types.isTerminalEquivUnique _ ht
  have hm : Mono (E.map (terminal.from H)) := inferInstance
  exact Function.Injective.subsingleton (f := E.map (terminal.from H))
    ((CategoryTheory.mono_iff_injective _).mp hm)

/-- A subterminal étale sheaf has an open support with the section factorization property.
Source: Stacks Project, Étale Cohomology, Tag 04HV, lemma-support-subsheaf-final.
(blueprint: lem-weil-pbc-etale-subsheaf-final-open-parts-factorization)

Proof: Monicity into the terminal sheaf makes each section set a subsingleton. Take the
union of the images of all étale objects with a section. Étale maps are open, so the union
is open. A section implies factorization through this union. Conversely, for an object
factoring through it, the pullbacks of the objects used in the union form a jointly
surjective étale covering. Pull back their sections. They agree on every overlap by
subsingletonness; sheaf gluing gives a section on the object, unique by subsingletonness.
If factorization fails, any section would imply factorization, so the section set is empty.
This also handles empty objects: the empty covering supplies their unique section. -/
theorem exists_open_etale_subsheaf_final_factorization (S : Scheme.{u})
    (H : Sheaf S.smallEtaleTopology (Type (max u v)))
    [Mono (terminal.from H)] :
    ∃ W : S.Opens, etaleSubsheafFactorization S H W := by
  classical
  let I := Σ U : S.Etale, H.obj.obj (op U)
  let image (i : I) : S.Opens := ⟨Set.range i.1.hom, i.1.hom.isOpenMap.isOpen_range⟩
  let W : S.Opens := ⨆ i : I, image i
  have factor (U : S.Etale) (s : H.obj.obj (op U)) :
      ∃ f : U.left ⟶ W.toScheme, f ≫ W.ι = U.hom := by
    have hr : Set.range U.hom ⊆ (W : Set S) := by
      intro x hx
      exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨U, s⟩, hx⟩
    have hr' : Set.range U.hom ⊆ Set.range W.ι := by
      simpa only [Opens.range_ι] using hr
    exact ⟨IsOpenImmersion.lift W.ι U.hom hr',
      IsOpenImmersion.lift_fac W.ι U.hom hr'⟩
  refine ⟨W, fun U => ?_⟩
  have : Subsingleton (H.obj.obj (op U)) := section_subsingleton S H U
  constructor
  · constructor
    · rintro ⟨h⟩
      exact factor U h.default
    · rintro ⟨f, hf⟩
      let Z (i : I) : S.Etale :=
        Etale.mk (pullback.fst i.1.hom U.hom ≫ i.1.hom)
      let a (i : I) : Z i ⟶ U :=
        MorphismProperty.Over.homMk (pullback.snd i.1.hom U.hom) (by
          exact pullback.condition.symm)
      let b (i : I) : Z i ⟶ i.1 :=
        MorphismProperty.Over.homMk (pullback.fst i.1.hom U.hom) rfl
      have hc : Sieve.ofArrows Z a ∈ S.smallEtaleTopology U := by
        apply (ofArrows_mem_smallEtaleTopology_iff a).mpr
        apply Set.eq_univ_of_forall
        intro x
        have hx : U.hom x ∈ W := by
          have he := congrArg (fun g : U.left ⟶ S => g x) hf
          change W.ι (f x) = U.hom x at he
          exact he ▸ (f x).property
        obtain ⟨i, y, hy⟩ := (TopologicalSpace.Opens.mem_iSup).mp hx
        obtain ⟨z, hz, hz'⟩ := Pullback.exists_preimage_pullback y x hy
        exact Set.mem_iUnion.mpr ⟨i, z, hz'⟩
      let s (i : I) : PUnit.{max u v + 1} ⟶ H.obj.obj (op (Z i)) :=
        ↾fun _ => H.obj.map (b i).op i.2
      have compat {T : S.Etale} {i j : I} (c : T ⟶ Z i) (d : T ⟶ Z j)
          (_ : c ≫ a i = d ≫ a j) :
          s i ≫ H.obj.map c.op = s j ≫ H.obj.map d.op := by
        have : Subsingleton (H.obj.obj (op T)) := section_subsingleton S H T
        apply ConcreteCategory.hom_ext
        intro x
        exact Subsingleton.elim _ _
      have t := H.property.amalgamateOfArrows a hc s (@compat)
      exact ⟨⟨⟨t PUnit.unit⟩, fun x => Subsingleton.elim _ _⟩⟩
  · intro hn
    exact ⟨fun s => hn (factor U s)⟩

end AlgebraicGeometry.Scheme
