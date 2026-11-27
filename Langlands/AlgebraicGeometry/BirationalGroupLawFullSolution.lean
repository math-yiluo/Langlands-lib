import Langlands.AlgebraicGeometry.BirationalGroupLawGenericComparison

/-! # Multiplication compatibility after extending a solution embedding -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.BirationalGroupLaw.Solution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {S X : Scheme.{u}} {f : X ⟶ S} {m : BirationalGroupLaw f}

set_option maxHeartbeats 700000 in
/-- An open immersion extending the common chart gives a solution with domain all of `X`. -/
theorem exists_full_of_extension [S.IsSeparated] [IsReduced S] [Smooth f] (σ : m.Solution)
    (τ : X ⟶ σ.group.X.left) [IsOpenImmersion τ]
    (hτ : τ ≫ σ.group.X.hom = f) (hchart : σ.domain.ι ≫ τ = σ.embedding) :
    ∃ σ' : m.Solution, σ'.domain = ⊤ := by
  let A := Over.mk f
  let v : A ⟶ σ.group.X := Over.homMk τ hτ
  let p : m.overDomain ⟶ A := m.overInclusion ≫ fst A A
  let q : m.overDomain ⟶ A := m.overInclusion ≫ snd A A
  let D := m.domain.toScheme
  let p₁ : D ⟶ X := m.domain.ι ≫ pullback.fst f f
  let p₂ : D ⟶ X := m.domain.ι ≫ pullback.snd f f
  have hp₁ : Smooth p₁ := by dsimp [p₁]; infer_instance
  have hp₂ : Smooth p₂ := by dsimp [p₂]; infer_instance
  have : IsOpenImmersion (leftTranslation f m.domain m.mul m.mul_comp) := m.isOpenImmersion_leftTranslation
  have he : leftTranslation f m.domain m.mul m.mul_comp ≫ pullback.snd f f = m.mul := pullback.lift_snd ..
  have hm : Smooth m.mul := by rw [← he]; infer_instance
  have hD : Smooth m.overDomain.hom := inferInstanceAs (Smooth (p₁ ≫ f))
  have : IsReduced D := SmoothReducedBase.isReduced_of_smooth_of_isReduced m.overDomain.hom
  have : IsSeparated σ.group.X.hom := σ.isSeparated
  have : σ.group.X.left.IsSeparated := separatedScheme_of_separated_over σ.group.X.hom
  let V₁ := p₁ ⁻¹ᵁ σ.domain
  let V₂ := p₂ ⁻¹ᵁ σ.domain
  let V₃ := m.mul ⁻¹ᵁ σ.domain
  let W := V₁ ⊓ V₂ ⊓ V₃
  have hd₁ : Dense (V₁ : Set D) := σ.domain_dense.dense.preimage p₁.isOpenMap
  have hd₂ : Dense (V₂ : Set D) := σ.domain_dense.dense.preimage p₂.isOpenMap
  have hd₃ : Dense (V₃ : Set D) := σ.domain_dense.dense.preimage m.mul.isOpenMap
  have : IsDominant W.ι := Opens.isDominant_ι ((hd₁.inter_of_isOpen_left hd₂ V₁.isOpen).inter_of_isOpen_left
    hd₃ (V₁ ⊓ V₂).isOpen)
  have hv : σ.firstChart ≫ v = σ.secondChart := Over.OverMorphism.ext hchart
  have hprod : lift (p ≫ v) (q ≫ v) ≫ μ[σ.group.X] = m.overMul ≫ v := by
    apply Over.OverMorphism.ext
    apply AlgebraicGeometry.ext_of_isDominant W.ι
    let T := Over.mk (W.ι ≫ m.overDomain.hom)
    let w : T ⟶ m.overDomain := Over.homMk W.ι rfl
    have factor (s : m.overDomain ⟶ A) (hs : W ≤ s.left ⁻¹ᵁ σ.domain) :
        ∃ t : T ⟶ σ.overChart, w ≫ s = t ≫ σ.firstChart := by
      let t := D.homOfLE hs ≫ s.left ∣_ σ.domain
      have ht : t ≫ σ.domain.ι = W.ι ≫ s.left := by
        dsimp only [t]
        rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
      refine ⟨Over.homMk t (by
        change t ≫ σ.domain.ι ≫ f = W.ι ≫ m.overDomain.hom
        rw [← Category.assoc, ht, Category.assoc]
        exact congrArg (fun t => W.ι ≫ t) s.w), Over.OverMorphism.ext ht.symm⟩
    obtain ⟨a, ha⟩ := factor p (inf_le_left.trans inf_le_left : W ≤ V₁)
    obtain ⟨b, hb⟩ := factor q (inf_le_left.trans inf_le_right : W ≤ V₂)
    obtain ⟨c, hc⟩ := factor m.overMul (inf_le_right : W ≤ V₃)
    have he := σ.mul_eq_over w a b c ha hb hc
    have h' : w ≫ (lift (p ≫ v) (q ≫ v) ≫ μ[σ.group.X]) = w ≫ (m.overMul ≫ v) := by
      rw [← Category.assoc w, comp_lift, ← Category.assoc w p, ← Category.assoc w q,
        ← Category.assoc w m.overMul, ha, hb, hc]
      simpa only [Category.assoc, hv] using he
    exact congrArg Over.Hom.left h'
  let U' : X.Opens := ⊤
  let j := U'.ι ≫ τ
  have hj : j ≫ σ.group.X.hom = U'.ι ≫ f := by dsimp [j]; rw [Category.assoc, hτ]
  have hji : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (U'.ι ≫ τ))
  let σ' : m.Solution := {
    group := σ.group
    smooth := σ.smooth
    isSeparated := σ.isSeparated
    locallyOfFiniteType := σ.locallyOfFiniteType
    quasiCompact := σ.quasiCompact
    domain := U'
    domain_dense := fun x => ⟨x, trivial, rfl, specializes_refl x⟩
    embedding := j
    embedding_comp := hj
    isOpenImmersion_embedding := hji
    embedding_dense := fun x => by
      obtain ⟨y, ⟨z, hz⟩, hgy, hyx⟩ := σ.embedding_dense x
      refine ⟨y, ⟨⟨σ.domain.ι z, trivial⟩, ?_⟩, hgy, hyx⟩
      have he := congrArg (fun e : σ.domain.toScheme ⟶ σ.group.X.left => e z) hchart
      exact he.trans hz
    mul_eq := by
      intro T a x y z hx hy hz
      let T₀ := Over.mk (x ≫ U'.ι ≫ f)
      let u : T₀ ⟶ m.overDomain := Over.homMk a (by
        change a ≫ m.domain.ι ≫ pullback.fst f f ≫ f = x ≫ U'.ι ≫ f
        rw [reassoc_of% hx])
      let a₁ : T₀ ⟶ A := Over.homMk (x ≫ U'.ι) (by
        change (x ≫ U'.ι) ≫ f = x ≫ U'.ι ≫ f
        rw [Category.assoc])
      let a₂ : T₀ ⟶ A := Over.homMk (y ≫ U'.ι) (by
        change (y ≫ U'.ι) ≫ f = x ≫ U'.ι ≫ f
        rw [Category.assoc, ← reassoc_of% hy, ← reassoc_of% hx, pullback.condition])
      let a₃ : T₀ ⟶ A := Over.homMk (z ≫ U'.ι) (by
        change (z ≫ U'.ι) ≫ f = x ≫ U'.ι ≫ f
        rw [← hz, Category.assoc, m.mul_comp, ← reassoc_of% hx])
      have h₁ : u ≫ p = a₁ := Over.OverMorphism.ext hx
      have h₂ : u ≫ q = a₂ := Over.OverMorphism.ext hy
      have h₃ : u ≫ m.overMul = a₃ := Over.OverMorphism.ext hz
      have e := congrArg (fun t => u ≫ t) hprod
      rw [← Category.assoc u, comp_lift, ← Category.assoc u p, ← Category.assoc u q,
        ← Category.assoc u m.overMul, h₁, h₂, h₃] at e
      exact congrArg Over.Hom.left e.symm }
  exact ⟨σ', rfl⟩

end Langlands.AlgebraicGeometry.BirationalGroupLaw.Solution
