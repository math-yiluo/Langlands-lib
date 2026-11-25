/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Morphisms into a coproduct of copies of a scheme

Source: Stacks Project, Groupoids, Example 03YW and Schemes, Lemmas 01JB and 01HI
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An indexed clopen decomposition consists of pairwise disjoint open subschemes whose
union is the whole scheme. Each piece is also closed, since its complement is the union
of the other pieces. Source: Stacks Project, Groupoids, Example 03YW
(auxiliary; not a blueprint node). -/
def IsClopenDecomposition (W : Scheme.{u}) (E : Type v) (P : E → W.Opens) : Prop :=
  (∀ e e' : E, e ≠ e' → Disjoint (P e) (P e')) ∧ (⨆ e, P e) = ⊤

open Classical in
/-- Source: Stacks Project, Groupoids, Example 03YW, and Schemes, Lemmas 01JB and 01HI
(auxiliary; not a blueprint node).

The coprojections are open immersions with disjoint images covering the coproduct.
Pulling their images back along a map over `U` gives disjoint open pieces covering `W`;
their complements are unions of the other pieces. On each piece the map factors through
the corresponding coprojection, and its factor is forced by the map to `U`.
Conversely, map each open piece through its coprojection and glue the maps. The empty
overlaps make gluing automatic, while the open cover makes the glued map unique and
forces its component preimages. A decomposition is equivalently a locally constant
function to the discrete index type. The constant and empty-index cases follow from
these constructions. -/
theorem coproductCopiesMorphismsClopen (U W : Scheme.{u}) (E : Type v) [Small.{u} E]
    (s : W ⟶ U) :
    ((∀ f : W ⟶ ∐ fun _ : E => U,
      f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s →
        IsClopenDecomposition W E
          (fun e => f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) ∧
        ∀ e : E,
          (f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange).ι ≫ f =
            ((f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange).ι ≫ s) ≫
              Sigma.ι (fun _ : E => U) e)) ∧
    (∀ P : E → W.Opens, IsClopenDecomposition W E P →
      ∃! f : W ⟶ ∐ fun _ : E => U,
        f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s ∧
          ∀ e : E, f ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange = P e) ∧
    (∃ b : {f : W ⟶ ∐ fun _ : E => U //
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s} ≃
          {P : E → W.Opens // IsClopenDecomposition W E P},
      ∀ f e, (b f).1 e = f.1 ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) ∧
    (∃ b : {f : W ⟶ ∐ fun _ : E => U //
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s} ≃ LocallyConstant W E,
      ∀ f e, ((f.1 ⁻¹ᵁ (Sigma.ι (fun _ : E => U) e).opensRange) : Set W) =
        {x : W | b f x = e}) ∧
    ((∀ e₀ : E, ∀ e : E,
      ((s ≫ Sigma.ι (fun _ : E => U) e₀) ⁻¹ᵁ
        (Sigma.ι (fun _ : E => U) e).opensRange) =
          if e = e₀ then ⊤ else ⊥)) ∧
    (IsEmpty E →
      IsEmpty (∐ fun _ : E => U : Scheme.{u}) ∧
      ((∃ f : W ⟶ ∐ fun _ : E => U,
          f ≫ Sigma.desc (fun _ : E => 𝟙 U) = s) ↔ IsEmpty W)) := by
  classical
  let G : E → Scheme.{u} := fun _ ↦ U
  let π : (∐ G) ⟶ U := Sigma.desc (fun _ ↦ 𝟙 U)
  let pieces (f : W ⟶ ∐ G) : E → W.Opens :=
    fun e ↦ f ⁻¹ᵁ (Sigma.ι G e).opensRange
  have cover : ⨆ e, (Sigma.ι G e).opensRange = ⊤ :=
    (sigmaOpenCover G).iSup_opensRange
  have dec (f : W ⟶ ∐ G) : IsClopenDecomposition W E (pieces f) := by
    refine ⟨?_, f.iSup_preimage_eq_top cover⟩
    intro e e' h
    rw [disjoint_iff, ← f.preimage_inf,
      (disjoint_opensRange_sigmaι G e e' h).eq_bot, f.preimage_bot]
  have restriction (f : W ⟶ ∐ G) (hf : f ≫ π = s) (e : E) :
      (pieces f e).ι ≫ f = ((pieces f e).ι ≫ s) ≫ Sigma.ι G e := by
    let j := (pieces f e).ι
    have hr : Set.range (j ≫ f) ⊆ Set.range (Sigma.ι G e) := by
      rintro _ ⟨x, rfl⟩
      exact x.property
    let l := IsOpenImmersion.lift (Sigma.ι G e) (j ≫ f) hr
    have hl : l ≫ Sigma.ι G e = j ≫ f := IsOpenImmersion.lift_fac _ _ _
    have he : l = j ≫ s := by
      have := congrArg (fun t ↦ t ≫ π) hl
      simpa [π, G, Category.assoc, hf] using this
    rw [← hl, he]
  have colim (P : E → W.Opens) (hP : IsClopenDecomposition W E P) :
      IsColimit (Cofan.mk W (fun e ↦ (P e).ι)) := by
    apply Nonempty.some
    apply nonempty_isColimit_cofanMk_of
    · simpa using hP.2
    · intro e e' h
      simpa using hP.1 e e' h
  have unique (P : E → W.Opens) (hP : IsClopenDecomposition W E P) :
      ∃! f : W ⟶ ∐ G, f ≫ π = s ∧ ∀ e, pieces f e = P e := by
    let c := colim P hP
    let f := c.desc (Cofan.mk (∐ G) (fun e ↦ ((P e).ι ≫ s) ≫ Sigma.ι G e))
    have fac (e : E) : (P e).ι ≫ f = ((P e).ι ≫ s) ≫ Sigma.ι G e :=
      c.fac _ ⟨e⟩
    have pre (e : E) : pieces f e = P e := by
      ext x
      obtain ⟨e', hx⟩ : ∃ e', x ∈ P e' := by
        have : x ∈ ⨆ e, P e := by rw [hP.2]; trivial
        exact TopologicalSpace.Opens.mem_iSup.mp this
      have fx : f x = Sigma.ι G e' (s x) := by
        have := congrArg (fun t : (P e').toScheme ⟶ ∐ G ↦ t ⟨x, hx⟩) (fac e')
        exact this
      change (∃ y, Sigma.ι G e y = f x) ↔ x ∈ P e
      rw [fx]
      constructor
      · rintro ⟨y, hy⟩
        have he : e = e' := congrArg Sigma.fst ((sigmaι_eq_iff G e e' y (s x)).mp hy)
        simpa [he] using hx
      · intro he
        have hee : e = e' := by
          by_contra hn
          exact (hP.1 e e' hn).le_bot ⟨he, hx⟩
        subst e'
        exact ⟨s x, rfl⟩
    have over : f ≫ π = s := by
      apply c.hom_ext
      intro j
      obtain ⟨e⟩ := j
      simpa [Category.assoc, π] using congrArg (fun t ↦ t ≫ π) (fac e)
    refine ⟨f, ⟨over, pre⟩, ?_⟩
    intro g hg
    apply c.hom_ext
    intro j
    obtain ⟨e⟩ := j
    have r := restriction g hg.1 e
    rw [hg.2 e] at r
    exact r.trans (fac e).symm
  let toD : {f : W ⟶ ∐ G // f ≫ π = s} →
      {P : E → W.Opens // IsClopenDecomposition W E P} :=
    fun f ↦ ⟨pieces f.1, dec f.1⟩
  have bij : Function.Bijective toD := by
    constructor
    · intro f g h
      apply Subtype.ext
      have eqP : pieces g.1 = pieces f.1 := (congrArg Subtype.val h).symm
      obtain ⟨k, hk, hu⟩ := unique (pieces f.1) (dec f.1)
      exact (hu f.1 ⟨f.2, fun _ ↦ rfl⟩).trans
        (hu g.1 ⟨g.2, congrFun eqP⟩).symm
    · intro P
      obtain ⟨f, hf, _⟩ := unique P.1 P.2
      exact ⟨⟨f, hf.1⟩, Subtype.ext (funext hf.2)⟩
  let b := Equiv.ofBijective toD bij
  have constants (e₀ e : E) : pieces (s ≫ Sigma.ι G e₀) e =
      if e = e₀ then ⊤ else ⊥ := by
    ext x
    change (∃ y, Sigma.ι G e y = (s ≫ Sigma.ι G e₀) x) ↔ _
    rw [Scheme.Hom.comp_apply]
    by_cases h : e = e₀
    · subst e
      simp only [↓reduceIte]
      exact iff_of_true ⟨s x, rfl⟩ trivial
    · simp only [h, ↓reduceIte]
      change (∃ y, Sigma.ι G e y = Sigma.ι G e₀ (s x)) ↔ False
      refine ⟨?_, False.elim⟩
      rintro ⟨y, hy⟩
      exact h (congrArg Sigma.fst ((sigmaι_eq_iff G e e₀ y (s x)).mp hy))
  have emptyCase : IsEmpty E → IsEmpty (∐ G : Scheme.{u}) ∧
      ((∃ f : W ⟶ ∐ G, f ≫ π = s) ↔ IsEmpty W) := by
    intro hE
    have : IsEmpty E := hE
    have hC : IsEmpty (∐ G : Scheme.{u}) := by
      refine ⟨fun x ↦ ?_⟩
      obtain ⟨e, _, _⟩ := (sigmaOpenCover G).exists_eq x
      change E at e
      exact isEmptyElim e
    refine ⟨hC, ?_⟩
    constructor
    · rintro ⟨f, _⟩
      exact ⟨fun x ↦ hC.false (f x)⟩
    · intro hW
      have : IsEmpty W := hW
      exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _⟩
  refine ⟨fun f hf ↦ ⟨dec f, restriction f hf⟩, unique,
    ⟨b, fun _ _ ↦ rfl⟩, ?_, constants, emptyCase⟩
  let fibers (l : LocallyConstant W E) : E → W.Opens :=
    fun e ↦ ⟨{x | l x = e}, l.isLocallyConstant.isOpen_fiber e⟩
  have fibersDec (l : LocallyConstant W E) : IsClopenDecomposition W E (fibers l) := by
    refine ⟨?_, ?_⟩
    · intro e e' h
      rw [disjoint_iff]
      ext x
      change (l x = e ∧ l x = e') ↔ False
      exact ⟨fun hx ↦ h (hx.1.symm.trans hx.2), False.elim⟩
    · apply top_unique
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l x, rfl⟩
  let fromLC : LocallyConstant W E →
      {P : E → W.Opens // IsClopenDecomposition W E P} :=
    fun l ↦ ⟨fibers l, fibersDec l⟩
  have fibersBij : Function.Bijective fromLC := by
    constructor
    · intro l l' h
      apply LocallyConstant.ext
      intro x
      have he := congrFun (congrArg Subtype.val h) (l x)
      change fibers l (l x) = fibers l' (l x) at he
      have hx : x ∈ fibers l' (l x) := by rw [← he]; exact rfl
      exact hx.symm
    · intro P
      have existsIndex (x : W) : ∃ e, x ∈ P.1 e := by
        have hx : x ∈ ⨆ e, P.1 e := by rw [P.2.2]; trivial
        exact TopologicalSpace.Opens.mem_iSup.mp hx
      let φ : W → E := fun x ↦ (existsIndex x).choose
      have memφ (x : W) : x ∈ P.1 (φ x) := (existsIndex x).choose_spec
      have mem_iff (x : W) (e : E) : φ x = e ↔ x ∈ P.1 e := by
        constructor
        · intro h
          rw [← h]
          exact memφ x
        · intro hx
          by_contra hn
          exact (P.2.1 (φ x) e hn).le_bot ⟨memφ x, hx⟩
      let l : LocallyConstant W E := ⟨φ, IsLocallyConstant.iff_isOpen_fiber.mpr
        (fun e ↦ by
          have he : φ ⁻¹' {e} = (P.1 e : Set W) := by
            ext x
            exact mem_iff x e
          rw [he]
          exact (P.1 e).isOpen)⟩
      refine ⟨l, Subtype.ext ?_⟩
      funext e
      ext x
      exact mem_iff x e
  let d := Equiv.ofBijective fromLC fibersBij
  refine ⟨b.trans d.symm, ?_⟩
  intro f e
  have he := congrFun (congrArg Subtype.val (d.apply_symm_apply (b f))) e
  exact (congrArg (fun V : W.Opens ↦ (V : Set W)) he).symm

end AlgebraicGeometry
