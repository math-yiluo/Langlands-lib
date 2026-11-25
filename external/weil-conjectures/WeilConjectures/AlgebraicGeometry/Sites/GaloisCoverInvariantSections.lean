/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal

/-!
# Invariant sections descend along a Galois cover

Let `c: P ⟶ V` be a finite étale Galois cover with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover`) and `E` a sheaf of sets on the small étale site of `V`.
The group `G` acts on the sections `E(P)` of `E` over the étale `V`-scheme `P`, by restriction
along the automorphisms `c.smul g`. A section over `P` which is invariant under this action is
the restriction of a unique section over `V`: two morphisms `p₁, p₂: Z ⟶ P` over `V` differ,
locally on `Z`, by an element of `G`, since the graphs `(g • -, id): P ⟶ P ×_V P` cover the
fibre product.

## Main statements

- `AlgebraicGeometry.Scheme.GaloisCover.exists_map_eq_of_forall_smul`: a `G`-invariant section
  of a sheaf of sets over `P` descends to `V`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {G : Type (u + 1)} [Group G] [Finite G] (c : V.GaloisCover G)

attribute [local instance] GaloisCover.etale GaloisCover.surjective

/-- The total space of a Galois cover, as an object of the small étale site of the base. -/
noncomputable abbrev etaleObj : V.Etale :=
  Scheme.Etale.mk c.π

/-- The action of `g: G` on the total space of a Galois cover, as an endomorphism in the small
étale site of the base. -/
noncomputable def smulEtale (g : G) : c.etaleObj ⟶ c.etaleObj :=
  MorphismProperty.Over.homMk (c.smul g) (c.smul_π g)

@[simp]
lemma smulEtale_left (g : G) : (c.smulEtale g).left = c.smul g :=
  rfl

/-- The unit of `G` acts trivially on the total space of a Galois cover, as an object of the
small étale site. -/
lemma smulEtale_one : c.smulEtale 1 = 𝟙 _ :=
  EtaleTorsor.etaleHom_ext c.one_smul

/-- The action of `G` on the total space of a Galois cover, as an object of the small étale
site, is a left action. -/
lemma smulEtale_mul (g h : G) : c.smulEtale (g * h) = c.smulEtale h ≫ c.smulEtale g :=
  EtaleTorsor.etaleHom_ext (c.mul_smul g h)

/-- The graph `(g • -, id): P ⟶ P ×_V P` of the action of `g` on a Galois cover. -/
noncomputable def graph (g : G) : c.P ⟶ pullback c.π c.π :=
  pullback.lift (c.smul g) (𝟙 _) (by simp [c.smul_π])

lemma graph_eq (g : G) :
    c.graph g = Sigma.ι (fun _ : G ↦ c.P) g ≫ Sigma.desc fun g : G ↦
      pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π]) :=
  (Sigma.ι_comp_desc _ _).symm

instance isOpenImmersion_graph (g : G) : IsOpenImmersion (c.graph g) := by
  have := c.isIso_sigmaDesc
  rw [graph_eq]
  infer_instance

/-- The graphs of the action of `G` on a Galois cover cover the fibre product `P ×_V P`. -/
lemma exists_graph_apply_eq (w : ↥(pullback c.π c.π)) : ∃ (g : G) (x : c.P), c.graph g x = w := by
  have := c.isIso_sigmaDesc
  let d := Sigma.desc fun g : G ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π])
  obtain ⟨x, hx⟩ := (sigmaOpenCover fun _ : G ↦ c.P).covers (inv d w)
  refine ⟨(sigmaOpenCover fun _ : G ↦ c.P).idx (inv d w), x, ?_⟩
  rw [graph_eq, Scheme.Hom.comp_apply]
  erw [hx]
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

variable {c} in
/-- Two morphisms `p₁, p₂: Z ⟶ P` over `V` into a Galois cover differ by the action of `g`
on the open subscheme `Z ×_{P ×_V P} P` of `Z` where `(p₁, p₂)` meets the graph of `g`. -/
lemma pullback_fst_comp_eq_snd_comp_smul {Z : Scheme.{u}} {p₁ p₂ : Z ⟶ c.P}
    (h : p₁ ≫ c.π = p₂ ≫ c.π) (g : G) :
    pullback.fst (pullback.lift p₁ p₂ h) (c.graph g) ≫ p₁ =
      pullback.snd (pullback.lift p₁ p₂ h) (c.graph g) ≫ c.smul g := by
  have := congrArg (· ≫ pullback.fst c.π c.π) (pullback.condition (f := pullback.lift p₁ p₂ h)
    (g := c.graph g))
  simpa [graph] using this

variable {c} in
/-- The second projection of `Z ×_{P ×_V P} P`, for the graph of `g`, is the restriction of `p₂`. -/
lemma pullback_fst_comp_eq_snd {Z : Scheme.{u}} {p₁ p₂ : Z ⟶ c.P}
    (h : p₁ ≫ c.π = p₂ ≫ c.π) (g : G) :
    pullback.fst (pullback.lift p₁ p₂ h) (c.graph g) ≫ p₂ =
      pullback.snd (pullback.lift p₁ p₂ h) (c.graph g) := by
  have := congrArg (· ≫ pullback.snd c.π c.π) (pullback.condition (f := pullback.lift p₁ p₂ h)
    (g := c.graph g))
  simpa [graph] using this

variable {c} in
/-- The open subschemes `Z ×_{P ×_V P} P` for the graphs of the elements of `G` cover `Z`. -/
lemma iUnion_range_pullback_fst_graph {Z : Scheme.{u}} {p₁ p₂ : Z ⟶ c.P}
    (h : p₁ ≫ c.π = p₂ ≫ c.π) :
    ⋃ g : G, Set.range (pullback.fst (pullback.lift p₁ p₂ h) (c.graph g)) = Set.univ := by
  refine Set.eq_univ_of_forall fun z ↦ ?_
  obtain ⟨g, x, hx⟩ := c.exists_graph_apply_eq (pullback.lift p₁ p₂ h z)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback z x hx.symm
  exact Set.mem_iUnion.2 ⟨g, w, hw⟩

/-- The morphism from the total space of a Galois cover to the terminal object of the small
étale site of the base is surjective. -/
lemma surjective_terminal_from_left : Function.Surjective (terminal.from c.etaleObj).left := by
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale V
  let e : Scheme.Etale.mk (𝟙 V) ≅ ⊤_ V.Etale := hT.uniqueUpToIso terminalIsTerminal
  have he : terminal.from c.etaleObj = hT.from c.etaleObj ≫ e.hom := terminal.hom_ext _ _
  have h₁ : (hT.from c.etaleObj).left = c.π := by
    exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (hT.from c.etaleObj))
  have : IsIso e.hom.left :=
    ⟨e.inv.left, congrArg (·.left) e.hom_inv_id, congrArg (·.left) e.inv_hom_id⟩
  rw [he, Etale.comp_left_eq, h₁, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact e.hom.left.homeomorph.surjective.comp c.surjective.surj

/-- **Galois descent of invariant sections**: a section of a sheaf of sets on the small étale
site of `V` over the total space of a Galois cover which is invariant under the action of the group
is the restriction of a section over `V`. -/
theorem exists_map_eq_of_forall_smul {E : V.Etaleᵒᵖ ⥤ Type w}
    (hE : Presheaf.IsSheaf V.smallEtaleTopology E) (x : E.obj (op c.etaleObj))
    (hx : ∀ g : G, E.map (c.smulEtale g).op x = x) :
    ∃ y : E.obj (op (⊤_ V.Etale)), E.map (terminal.from c.etaleObj).op y = x := by
  refine Etale.exists_map_eq_of_surjective hE _ c.surjective_terminal_from_left x
    fun {Z} p₁ p₂ _ ↦ ?_
  have h : p₁.left ≫ c.π = p₂.left ≫ c.π :=
    (MorphismProperty.Over.w p₁).trans (MorphismProperty.Over.w p₂).symm
  let Zg (g : G) : V.Etale := Scheme.Etale.mk
    (pullback.fst (pullback.lift p₁.left p₂.left h) (c.graph g) ≫ Z.hom)
  let ιg (g : G) : Zg g ⟶ Z := MorphismProperty.Over.homMk
    (pullback.fst (pullback.lift p₁.left p₂.left h) (c.graph g)) rfl
  have hsep : Presieve.IsSeparatedFor E (Presieve.ofArrows Zg ιg) := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 hE _
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff ιg).2
        (iUnion_range_pullback_fst_graph h))).isSeparatedFor
  refine hsep.ext fun _ f hf ↦ ?_
  obtain ⟨g⟩ := hf
  have hw : pullback.snd (pullback.lift p₁.left p₂.left h) (c.graph g) ≫ c.etaleObj.hom =
      (Zg g).hom := by
    rw [← pullback_fst_comp_eq_snd h g, Category.assoc, MorphismProperty.Over.w p₂]
    rfl
  let sg : Zg g ⟶ c.etaleObj := MorphismProperty.Over.homMk _ hw
  have h₁ : ιg g ≫ p₁ = sg ≫ c.smulEtale g :=
    EtaleTorsor.etaleHom_ext (pullback_fst_comp_eq_snd_comp_smul h g)
  have h₂ : ιg g ≫ p₂ = sg :=
    EtaleTorsor.etaleHom_ext (pullback_fst_comp_eq_snd h g)
  rw [← Functor.map_comp_apply, ← op_comp, h₁, ← Functor.map_comp_apply, ← op_comp, h₂,
    op_comp, Functor.map_comp_apply, hx]

end AlgebraicGeometry.Scheme.GaloisCover
