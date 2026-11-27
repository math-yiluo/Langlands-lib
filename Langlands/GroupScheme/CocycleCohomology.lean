import Langlands.GroupScheme.CocycleRelativeTrivialization

/-! # Cohomology of natural group-scheme cocycles on a fixed cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G H : GroupScheme S} {U V : Over S}

/-- Two cocycles on the same cover are cohomologous if the second is a twist of the first. -/
def Cohomologous (ξ ζ : Cocycle G U) : Prop :=
  ∃ f : U ⟶ G.X, ∀ {Z : Over S} (a b : Z ⟶ U),
    ζ.toFun a b = (ξ.twist f).toFun a b

/-- The unit cochain gives reflexivity. -/
theorem Cohomologous.refl (ξ : Cocycle G U) : ξ.Cohomologous ξ := by
  refine ⟨1, fun a b => ?_⟩
  simp only [twist, MonObj.comp_one, inv_one, one_mul, mul_one]

/-- Inverting the cochain reverses a cohomology relation. -/
theorem Cohomologous.symm {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ) :
    ζ.Cohomologous ξ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f⁻¹, fun a b => ?_⟩
  change ξ.toFun a b = (a ≫ f⁻¹)⁻¹ * ζ.toFun a b * (b ≫ f⁻¹)
  rw [hf]
  simp only [twist, GrpObj.comp_inv]
  group

/-- Multiplying the two cochains composes cohomology relations. -/
theorem Cohomologous.trans {ξ ζ ν : Cocycle G U}
    (h : ξ.Cohomologous ζ) (h' : ζ.Cohomologous ν) : ξ.Cohomologous ν := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  refine ⟨f * g, fun a b => ?_⟩
  rw [hg]
  change (a ≫ g)⁻¹ * ζ.toFun a b * (b ≫ g) =
    (a ≫ (f * g))⁻¹ * ξ.toFun a b * (b ≫ (f * g))
  rw [hf]
  simp only [twist, MonObj.comp_mul]
  group

/-- The cochain-orbit equivalence relation on cocycles on a fixed cover. -/
def cohomologySetoid (G : GroupScheme S) (U : Over S) : Setoid (Cocycle G U) where
  r := Cohomologous
  iseqv := ⟨Cohomologous.refl, Cohomologous.symm, Cohomologous.trans⟩

/-- Group homomorphisms preserve cohomology. -/
theorem Cohomologous.map {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ) (φ : G ⟶ H) :
    (ξ.map φ).Cohomologous (ζ.map φ) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ≫ φ.hom.hom, fun a b => ?_⟩
  change ζ.toFun a b ≫ φ.hom.hom =
    (a ≫ f ≫ φ.hom.hom)⁻¹ * (ξ.toFun a b ≫ φ.hom.hom) * (b ≫ f ≫ φ.hom.hom)
  rw [hf]
  simp only [twist, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

/-- Refining the cover preserves cohomology, using the restricted cochain. -/
theorem Cohomologous.refine {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ) (r : V ⟶ U) :
    (ξ.refine r).Cohomologous (ζ.refine r) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨r ≫ f, fun a b => ?_⟩
  simpa only [refine_toFun, twist, Category.assoc] using hf (a ≫ r) (b ≫ r)

/-- A cochain witnessing cohomology on an effective refinement descends to the original
cover. Epimorphy of the product refinement reflects the descended twist identity. -/
theorem Cohomologous.of_refine {ξ ζ : Cocycle G U} (r : V ⟶ U)
    [EffectiveEpi r.left] [Epi (r ⊗ₘ r).left]
    (h : (ξ.refine r).Cohomologous (ζ.refine r)) : ξ.Cohomologous ζ := by
  obtain ⟨f, hf⟩ := h
  have hrel {Z : Over S} (a b : Z ⟶ V) (hab : a ≫ r = b ≫ r) :
      a ≫ f = b ≫ f := by
    have hh := hf a b
    change ζ.toFun (a ≫ r) (b ≫ r) =
      (a ≫ f)⁻¹ * ξ.toFun (a ≫ r) (b ≫ r) * (b ≫ f) at hh
    rw [hab, toFun_self, toFun_self, mul_one] at hh
    exact inv_mul_eq_one.mp hh.symm
  let d : U.left ⟶ G.X.left :=
    EffectiveEpi.desc r.left f.left (fun {Z} a b hab => by
      have hb : b ≫ V.hom = a ≫ V.hom := by
        rw [← Over.w r, ← Category.assoc, ← Category.assoc, hab]
      let a₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk a rfl
      let b₀ : Over.mk (a ≫ V.hom) ⟶ V := Over.homMk b hb
      exact congrArg (fun e => e.left)
        (hrel a₀ b₀ (Over.OverMorphism.ext hab)))
  have hd : r.left ≫ d = f.left := EffectiveEpi.fac _ _ _
  let g : U ⟶ G.X := Over.homMk d (by
    apply (cancel_epi r.left).mp
    rw [← Category.assoc, hd, Over.w f, Over.w r])
  have hg : r ≫ g = f := Over.OverMorphism.ext hd
  refine ⟨g, ?_⟩
  apply toFun_eq_of_universal_eq ζ (ξ.twist g)
  apply Over.OverMorphism.ext
  apply (cancel_epi (r ⊗ₘ r).left).mp
  have hh := hf (fst V V) (snd V V)
  change ζ.toFun (fst V V ≫ r) (snd V V ≫ r) =
    (fst V V ≫ f)⁻¹ * ξ.toFun (fst V V ≫ r) (snd V V ≫ r) * (snd V V ≫ f) at hh
  have hcover : (r ⊗ₘ r) ≫ ζ.toFun (fst U U) (snd U U) =
      (r ⊗ₘ r) ≫ (ξ.twist g).toFun (fst U U) (snd U U) := by
    rw [← ζ.naturality, ← (ξ.twist g).naturality]
    simp only [tensorHom_fst, tensorHom_snd, twist, Category.assoc, hg]
    exact hh
  exact congrArg (fun e => e.left) hcover

/-- Cohomology of fixed-cover cocycles is reflected by every fpqc refinement. -/
theorem cohomologous_refine_iff (ξ ζ : Cocycle G U) (r : V ⟶ U)
    [QuasiCompact r.left] [Flat r.left] [Surjective r.left] :
    (ξ.refine r).Cohomologous (ζ.refine r) ↔ ξ.Cohomologous ζ := by
  have := effectiveEpi_tensorHom r
  exact ⟨fun h => h.of_refine r, fun h => h.refine r⟩

variable {S' : Scheme.{u}}

/-- Base change, with any compatible cover, preserves cohomology. -/
theorem Cohomologous.baseChange {ξ ζ : Cocycle G U} (h : ξ.Cohomologous ζ)
    (b : S' ⟶ S) (V : Over S') (r : (Over.map b).obj V ⟶ U) :
    (ξ.baseChange b V r).Cohomologous (ζ.baseChange b V r) := by
  obtain ⟨f, hf⟩ := h
  let g := (baseChangePointsEquiv b G V).symm (r ≫ f)
  refine ⟨g, fun {Z} a c => ?_⟩
  apply (baseChangePointsEquiv b G Z).injective
  change _ = baseChangePointsEquiv b G Z
    ((a ≫ g)⁻¹ * (ξ.baseChange b V r).toFun a c * (c ≫ g))
  rw [baseChange_toFun, map_mul, map_mul, map_inv, baseChangePointsEquiv_naturality,
    baseChangePointsEquiv_naturality, baseChange_toFun]
  simp only [g, MulEquiv.apply_symm_apply, ← Category.assoc]
  exact hf _ _

/-- A section of the cover trivializes its cocycle. -/
theorem isTrivial_of_section {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    (c : Cocycle G U) (s : Over.mk (𝟙 S) ⟶ U) : c.IsTrivial := by
  let q : U ⟶ Over.mk (𝟙 S) := Over.homMk U.hom
  refine ⟨c.toFun (𝟙 U) (q ≫ s), fun {Z} x y => ?_⟩
  have hq : x ≫ q = y ≫ q := Over.OverMorphism.ext ((Over.w x).trans (Over.w y).symm)
  rw [← c.naturality, ← c.naturality]
  simp only [Category.comp_id, ← Category.assoc, hq]
  exact eq_mul_inv_of_mul_eq (c.cocycle x y (y ≫ q ≫ s)).symm

end Langlands.GroupScheme.Cocycle
