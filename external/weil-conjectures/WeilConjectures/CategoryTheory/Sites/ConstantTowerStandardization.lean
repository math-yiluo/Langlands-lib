/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.DisjointGluing
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Standardising towers of constant sheaves on sites with disjoint refinements

An object `T` of a site has disjoint refinements
(`CategoryTheory.GrothendieckTopology.HasDisjointRefinements`) if every covering sieve of `T`
contains a disjoint covering family; this holds for the spectrum of a w-contractible ring in its
pro-étale site. When `T` is terminal and has disjoint refinements:

- `CategoryTheory.nonempty_iso_of_hasDisjointRefinements`: locally isomorphic sheaves are
  isomorphic;
- `CategoryTheory.exists_iso_comp_eq_constantSheaf_map`: an epimorphism `P_C ⟶ Q_C` of constant
  sheaves of modules (`P` finite) is a fixed `std : P ⟶ Q` up to an automorphism of `P_C`,
  provided every surjection `P ⟶ Q` is `std` up to an automorphism of `P`;
- `CategoryTheory.nonempty_iso_ofOpSequence_constantSheaf`: hence a tower of sheaves with
  epimorphic transitions, termwise isomorphic to constant sheaves `(Mₙ)_C`, is isomorphic to the
  standard tower `((Mₙ)_C, stdₙ)`.

Auxiliary results: `CategoryTheory.surjective_of_epi_constantSheaf_map` (constant sheaves detect
surjectivity over non-degenerate sites), `CategoryTheory.constantSheafOverHom_naturality`,
`CategoryTheory.epi_overPullback_map`.
-/

@[expose] public section

universe w v u v'

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type v'} [Ring Λ] [HasWeakSheafify J (ModuleCat.{v'} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)]

omit [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)] in
/-- The unit `M ⟶ Γ(T, M_C)` of the constant sheaf adjunction is the sheafification map. -/
lemma constantSheafAdj_unit_app_eq {T : C} (hT : IsTerminal T) (M : ModuleCat.{v'} Λ) :
    (constantSheafAdj J _ hT).unit.app M =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) := by
  have h := constantSheafAdj_homEquiv_apply J _ hT M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit] at h
  exact h.trans (Category.comp_id _)

/-- **Constant sheaves detect surjectivity over non-degenerate sites**: if the empty sieve does
not cover the terminal object and `M_C ⟶ N_C` is an epimorphism, then `f : M ⟶ N` is
surjective. -/
lemma surjective_of_epi_constantSheaf_map {T : C} (hT : IsTerminal T)
    (hbot : (⊥ : Sieve T) ∉ J T)
    {M N : ModuleCat.{v'} Λ} (f : M ⟶ N) [Epi ((constantSheaf J _).map f)] :
    Function.Surjective f := by
  rw [← ModuleCat.epi_iff_surjective]
  refine Abelian.epi_of_cokernel_π_eq_zero _ ?_
  have := (constantSheafAdj J (ModuleCat.{v'} Λ) hT).isLeftAdjoint
  have h0 : (constantSheaf J _).map (cokernel.π f) = 0 := by
    rw [← cancel_epi ((constantSheaf J _).map f), ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero]
  have hu : cokernel.π f ≫ (constantSheafAdj J _ hT).unit.app _ =
      (constantSheafAdj J _ hT).unit.app N ≫
        ((sheafSections J _).obj (op T)).map ((constantSheaf J _).map (cokernel.π f)) :=
    (constantSheafAdj J _ hT).unit.naturality (cokernel.π f)
  rw [h0, Functor.map_zero, comp_zero, constantSheafAdj_unit_app_eq] at hu
  ext x
  apply J.toSheafify_const_app_injective _ hbot
  have := congrArg (fun φ ↦ φ x) (congrArg ModuleCat.Hom.hom hu)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply] at this
  refine this.trans ?_
  exact (map_zero _).symm

section Naturality

variable {A : Type*} [Category* A] [HasWeakSheafify J A] (U : C) [HasWeakSheafify (J.over U) A]

/-- `constantSheafOverHom` is natural in the value of the constant sheaf. -/
lemma constantSheafOverHom_naturality {M N : A} (f : M ⟶ N) :
    (constantSheaf (J.over U) A).map f ≫ constantSheafOverHom J A U N =
      constantSheafOverHom J A U M ≫ (J.overPullback A U).map ((constantSheaf J A).map f) := by
  apply ((constantSheafAdj (J.over U) A Over.mkIdTerminal).homEquiv M _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    constantSheafAdj_homEquiv_constantSheafOverHom, constantSheafAdj_homEquiv_constantSheafOverHom]
  have h := NatTrans.congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) (op U)
  simp only [NatTrans.comp_app] at h
  exact h

end Naturality

section Over

variable [HasSheafify J (ModuleCat.{v'} Λ)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]
  (U : C) [(J.over U).HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]

omit [HasWeakSheafify J (ModuleCat.{v'} Λ)] in
/-- The restriction of sheaves to a localized site preserves epimorphisms (for concrete
coefficients in which epimorphisms of sheaves are the locally surjective morphisms). -/
lemma epi_overPullback_map {F G : Sheaf J (ModuleCat.{v'} Λ)} (φ : F ⟶ G) [Epi φ] :
    Epi ((J.overPullback (ModuleCat.{v'} Λ) U).map φ) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance
  have : Presheaf.IsLocallySurjective (J.over U)
      (Functor.whiskerLeft (Over.forget U).op φ.hom) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have : Sheaf.IsLocallySurjective ((J.overPullback (ModuleCat.{v'} Λ) U).map φ) := this
  infer_instance

end Over

/-- Over an object covered by the empty sieve, there is at most one morphism between the
restrictions of two sheaves. -/
lemma Sheaf.subsingleton_over_hom_of_bot_mem {A : Type*} [Category* A] (F G : Sheaf J A)
    {U : C} (hU : (⊥ : Sieve U) ∈ J U) : Subsingleton (F.over U ⟶ G.over U) :=
  Presieve.subsingleton_of_bot_mem (sheafHom F G).2 hU

/-- An object `T` of a site has **disjoint refinements** if every covering sieve of `T`
contains a disjoint covering family of `T` (e.g. `T` the spectrum of a w-contractible ring in
its pro-étale site). -/
def GrothendieckTopology.HasDisjointRefinements (T : C) : Prop :=
  ∀ S ∈ J T, ∃ (ι : Type w) (U : ι → C) (f : ∀ i, U i ⟶ T),
    Presieve.IsDisjointFamily f J ∧ Sieve.ofArrows U f ∈ J T ∧ ∀ i, S (f i)

/-- Over an object covered by the empty sieve, the restrictions of any two sheaves are
isomorphic (all their sections are terminal). -/
lemma Sheaf.nonempty_iso_over_of_bot_mem {A : Type*} [Category* A] (F G : Sheaf J A) {U : C}
    (hU : (⊥ : Sieve U) ∈ J U) : Nonempty (F.over U ≅ G.over U) := by
  have hV (V : Over U) : (⊥ : Sieve V) ∈ J.over U V := by
    rw [GrothendieckTopology.mem_over_iff, map_bot]
    simpa using J.pullback_stable V.hom hU
  let φ (F G : Sheaf J A) : F.over U ⟶ G.over U := ObjectProperty.homMk
    { app V := (Sheaf.isTerminalOfBotCover (G.over U) V.unop (hV _)).from _
      naturality _ _ _ := (Sheaf.isTerminalOfBotCover (G.over U) _ (hV _)).hom_ext _ _ }
  have := Sheaf.subsingleton_over_hom_of_bot_mem J F F hU
  have := Sheaf.subsingleton_over_hom_of_bot_mem J G G hU
  exact ⟨⟨φ F G, φ G F, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

/-- **Local isomorphisms glue on a site with disjoint refinements**: if two sheaves become
isomorphic over the members (not covered by the empty sieve) of a covering sieve of the terminal
object, which has disjoint refinements, then they are isomorphic. -/
theorem nonempty_iso_of_hasDisjointRefinements {A : Type*} [Category* A] {T : C}
    (hT : IsTerminal T) (hWC : J.HasDisjointRefinements.{w} T) (F G : Sheaf J A) {S : Sieve T}
    (hS : S ∈ J T)
    (h : ∀ ⦃U : C⦄ (g : U ⟶ T), S g → (⊥ : Sieve U) ∉ J U → Nonempty (F.over U ≅ G.over U)) :
    Nonempty (F ≅ G) := by
  obtain ⟨ι, U, f, hdisj, hcov, hSU⟩ := hWC S hS
  have key (i : ι) : Nonempty (F.over (U i) ≅ G.over (U i)) := by
    by_cases hb : (⊥ : Sieve (U i)) ∈ J (U i)
    · exact Sheaf.nonempty_iso_over_of_bot_mem J F G hb
    · exact h (f i) (hSU i) hb
  obtain ⟨e, -⟩ := hdisj.exists_iso_of_isTerminal hT hcov F G fun i ↦ (key i).some
  exact ⟨e⟩

section Standardization

variable [HasSheafify J (ModuleCat.{v'} Λ)]
  [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{v'} Λ)]
  [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{v'} Λ)]
  [∀ U : C, (J.over U).HasSheafCompose (CategoryTheory.forget (ModuleCat.{v'} Λ))]

/-- **Standardising an epimorphism of constant sheaves on a site with disjoint refinements.**
Let `std : P ⟶ Q` be a linear map, `P` finite, such that every surjective `f : P ⟶ Q` is `std`
up to an automorphism of `P` (e.g. reduction `(𝒪_E ⧸ ℓⁿ⁺¹)^r → (𝒪_E ⧸ ℓⁿ)^r`, by
`Module.Basis.exists_basis_map_eq`). On a site whose terminal object has disjoint refinements,
every epimorphism `ψ : P_C ⟶ Q_C` is `std` up to an automorphism of `P_C`: locally `ψ` is
induced by surjective linear maps, which are `std` up to automorphisms of `P`; these glue over
a disjoint refinement without compatibility conditions. -/
theorem exists_iso_comp_eq_constantSheaf_map {T : C} (hT : IsTerminal T)
    (hWC : J.HasDisjointRefinements.{w} T) {P Q : ModuleCat.{v'} Λ} [Module.Finite Λ P]
    (std : P ⟶ Q) (hstd : ∀ f : P ⟶ Q, Function.Surjective f → ∃ g : P ≅ P, g.hom ≫ f = std)
    (ψ : (constantSheaf J _).obj P ⟶ (constantSheaf J _).obj Q) [Epi ψ] :
    ∃ γ : (constantSheaf J _).obj P ≅ (constantSheaf J _).obj P,
      γ.hom ≫ ψ = (constantSheaf J _).map std := by
  obtain ⟨S, hS, hSf⟩ := exists_mem_forall_exists_constantSheafOverHom_comp_map_eq J P Q ψ
    (T := T)
  obtain ⟨ι, U, f, hdisj, hcov, hSU⟩ := hWC S hS
  have key (i : ι) : ∃ g : ((constantSheaf J _).obj P).over (U i) ≅
      ((constantSheaf J _).obj P).over (U i),
      g.hom ≫ (J.overPullback _ (U i)).map ψ =
        (J.overPullback _ (U i)).map ((constantSheaf J _).map std) := by
    by_cases hb : (⊥ : Sieve (U i)) ∈ J (U i)
    · have := Sheaf.subsingleton_over_hom_of_bot_mem J ((constantSheaf J _).obj P)
        ((constantSheaf J _).obj Q) hb
      exact ⟨Iso.refl _, Subsingleton.elim _ _⟩
    · obtain ⟨φ, hφ⟩ := hSf (f i) (hSU i) hb
      have := epi_overPullback_map J (U i) ψ
      have hepi : Epi ((constantSheaf (J.over (U i)) _).map φ) := by
        have : Epi ((constantSheaf (J.over (U i)) _).map φ ≫
            constantSheafOverHom J (ModuleCat.{v'} Λ) (U i) Q) := by
          rw [← hφ]
          infer_instance
        have h2 := epi_comp ((constantSheaf (J.over (U i)) _).map φ ≫
          constantSheafOverHom J (ModuleCat.{v'} Λ) (U i) Q)
          (inv (constantSheafOverHom J (ModuleCat.{v'} Λ) (U i) Q))
        simpa using h2
      have hbot : (⊥ : Sieve (Over.mk (𝟙 (U i)))) ∉ J.over (U i) (Over.mk (𝟙 (U i))) := by
        rw [GrothendieckTopology.mem_over_iff, map_bot]
        exact hb
      obtain ⟨g, hg⟩ := hstd φ
        (surjective_of_epi_constantSheaf_map (J.over (U i)) Over.mkIdTerminal hbot φ)
      refine ⟨(constantSheafOverIso J _ (U i) P).symm ≪≫ (constantSheaf _ _).mapIso g ≪≫
        constantSheafOverIso J _ (U i) P, ?_⟩
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
        constantSheafOverIso]
      rw [asIso_hom, hφ, ← Functor.map_comp_assoc, hg, constantSheafOverHom_naturality,
        asIso_inv, IsIso.inv_hom_id_assoc]
  choose g hg using key
  obtain ⟨γ, hγ⟩ := hdisj.exists_iso_of_isTerminal hT hcov _ _ g
  refine ⟨γ, ?_⟩
  obtain ⟨χ, -, hχ⟩ := hdisj.existsUnique_hom_of_isTerminal hT hcov
    ((constantSheaf J _).obj P) ((constantSheaf J _).obj Q)
    (fun i ↦ (J.overPullback _ (U i)).map ((constantSheaf J _).map std))
  exact (hχ _ fun i ↦ by rw [Functor.map_comp, hγ, hg]).trans (hχ _ fun i ↦ rfl).symm

/-- **Standardising a tower of constant sheaves.** On a site whose terminal object has disjoint
refinements, let `F` be a tower of sheaves with epimorphic transitions, each term isomorphic to
the constant sheaf at a finite module `Mₙ`, where every surjection `Mₙ₊₁ ⟶ Mₙ` is the standard
map `stdₙ` up to an automorphism of `Mₙ₊₁`. Then `F` is isomorphic to the tower of constant
sheaves with the standard transitions. -/
theorem nonempty_iso_ofOpSequence_constantSheaf {T : C} (hT : IsTerminal T)
    (hWC : J.HasDisjointRefinements.{w} T) (M : ℕ → ModuleCat.{v'} Λ) [∀ n, Module.Finite Λ (M n)]
    (std : ∀ n, M (n + 1) ⟶ M n)
    (hstd : ∀ n (f : M (n + 1) ⟶ M n), Function.Surjective f →
      ∃ g : M (n + 1) ≅ M (n + 1), g.hom ≫ f = std n)
    (F : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{v'} Λ)) (e : ∀ n, F.obj (op n) ≅ (constantSheaf J _).obj (M n))
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (n.le_add_right 1)).op)) :
    Nonempty (F ≅ Functor.ofOpSequence (X := fun n ↦ (constantSheaf J _).obj (M n))
      fun n ↦ (constantSheaf J _).map (std n)) := by
  have step (n : ℕ) (x : F.obj (op n) ≅ (constantSheaf J _).obj (M n)) :
      ∃ y : F.obj (op (n + 1)) ≅ (constantSheaf J _).obj (M (n + 1)),
        F.map (homOfLE (n.le_add_right 1)).op ≫ x.hom =
          y.hom ≫ (constantSheaf J _).map (std n) := by
    have : Epi ((e (n + 1)).inv ≫ F.map (homOfLE (n.le_add_right 1)).op ≫ x.hom) := by
      have := hF n
      infer_instance
    obtain ⟨γ, hγ⟩ := exists_iso_comp_eq_constantSheaf_map J hT hWC (std n) (hstd n)
      ((e (n + 1)).inv ≫ F.map (homOfLE (n.le_add_right 1)).op ≫ x.hom)
    refine ⟨e (n + 1) ≪≫ γ.symm, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hγ, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
  choose y hy using step
  let e' : ∀ n, F.obj (op n) ≅ (constantSheaf J _).obj (M n) := fun n ↦
    Nat.rec (motive := fun n ↦ F.obj (op n) ≅ (constantSheaf J _).obj (M n)) (e 0)
      (fun n x ↦ y n x) n
  let φ : F ⟶ Functor.ofOpSequence (X := fun n ↦ (constantSheaf J _).obj (M n))
      fun n ↦ (constantSheaf J _).map (std n) :=
    NatTrans.ofOpSequence (fun n ↦ (e' n).hom) fun n ↦ by
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact hy n (e' n)
  have : ∀ n, IsIso (φ.app n) := fun n ↦ inferInstanceAs (IsIso (e' n.unop).hom)
  have := NatIso.isIso_of_isIso_app φ
  exact ⟨asIso φ⟩

end Standardization

end CategoryTheory
