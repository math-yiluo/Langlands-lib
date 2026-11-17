import Langlands.GroupScheme.Absolute.BorelHomomorphismRigidityStatement
import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.HomogeneousQuotientBaseChange
import Langlands.GroupScheme.SimplyConnected.CoverPreimageDerived
import Langlands.AlgebraicGeometry.Units.FieldGlobalFunctions
import Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctionsAlgebra

/-! # Proof: homomorphisms agreeing on a Borel subgroup agree (Milne 17.21) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelHomomorphismRigidity

/-- A morphism to an affine scheme factors through any morphism inducing an isomorphism
on global functions. -/
theorem exists_factor_of_isIso_appTop {P P' Y : Scheme.{u}} (h : P ⟶ P') [IsIso h.appTop]
    [IsAffine Y] (ρ : P ⟶ Y) : ∃ τ : P' ⟶ Y, h ≫ τ = ρ := by
  refine ⟨P'.toSpecΓ ≫ Spec.map (ρ.appTop ≫ inv h.appTop) ≫ inv Y.toSpecΓ, ?_⟩
  rw [← cancel_mono Y.toSpecΓ]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, Scheme.toSpecΓ_naturality]

open Langlands.AlgebraicGeometry.Modules.DerivedSections in
/-- Over an algebraically closed field, a morphism from an integral scheme with a rational
point to a proper scheme becomes constant after composing with the canonical map to the
spectrum of global functions. -/
theorem toSpecΓ_comp_eq {k : Type u} [Field k] [IsAlgClosed k] {X Z : Scheme.{u}}
    [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X)
    (he : e ≫ p = 𝟙 _) (f : Z ⟶ Spec (CommRingCat.of k)) [IsProper f] (q : X ⟶ Z)
    (hq : q ≫ f = p) :
    q ≫ Z.toSpecΓ = p ≫ e ≫ q ≫ Z.toSpecΓ := by
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop]
  suffices hs : q.appTop = q.appTop ≫ e.appTop ≫ p.appTop by
    simp only [Category.assoc]
    rw [← hs]
  ext a
  let := Langlands.AlgebraicGeometry.Modules.GlobalFunctionsAlgebra.algebra f
  have hfin := Langlands.AlgebraicGeometry.Modules.FieldGlobalFunctions.finite_algebra f
  have ha : IsIntegral k a := Algebra.IsIntegral.isIntegral a
  let := Langlands.AlgebraicGeometry.Modules.GlobalFunctionsAlgebra.algebra p
  have hcomp : (algebraMap k Γ(X, ⊤)).comp (RingHom.id k) =
      q.appTop.hom.comp (algebraMap k Γ(Z, ⊤)) := by
    change (structureRingHom p).hom.comp (RingHom.id k) =
      q.appTop.hom.comp (structureRingHom f).hom
    rw [RingHom.comp_id, ← CommRingCat.hom_comp]
    simp only [structureRingHom, Category.assoc, ← Scheme.Hom.comp_appTop, hq]
  have hx : IsIntegral k (q.appTop a) :=
    IsIntegral.map_of_comp_eq (RingHom.id k) q.appTop.hom hcomp ha
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx))
  change q.appTop a = p.appTop (e.appTop (q.appTop a))
  rw [← hc]
  have hpe : ∀ y, e.appTop (p.appTop y) = y := by
    intro y
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    simp
  change (structureRingHom p).hom c = p.appTop (e.appTop ((structureRingHom p).hom c))
  rw [structureRingHom, CommRingCat.comp_apply, hpe]

end BorelHomomorphismRigidity

open BorelHomomorphismRigidity HomogeneousQuotientFromEmbedding
  Langlands.AlgebraicGeometry.FieldGlobalUnits in
/-- Milne, Proposition 17.21: homomorphisms of smooth connected affine groups over an
algebraically closed field which agree on a Borel subgroup after base change are equal. -/
theorem borelHomomorphismRigidity : BorelHomomorphismRigidityStatement.{u} := by
  intro k _ _ G G' _ _ _ _ _ _ B i hi R _ _ b φ₁ φ₂ hφ
  -- The quotient `G / B` and its properness.
  obtain ⟨Q, q, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B i hi.isClosedSubgroup hi.smooth
  let Q₀ : HomogeneousQuotient i := ⟨Q, q, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib⟩
  have hpar : IsParabolicSubgroup i :=
    ⟨hi.isClosedSubgroup, hi.smooth, ⟨_, _, 𝟙 _,
      borelAlgClosedFieldExtensionStatement k (AlgebraicClosure k) G inferInstance
        inferInstance inferInstance B i hi, Category.id_comp _⟩⟩
  have hprop : IsProper Q.hom :=
    parabolicSubgroupQuotientProper k G inferInstance B i hpar Q q hsep hlft hqc hsm hsurj
      hqqc hfib
  -- Base change of the quotient.
  let Q₁ := Q₀.baseChange b
  let j := (GroupScheme.baseChange b).map i
  let GR := (GroupScheme.baseChange b).obj G
  let GR' := (GroupScheme.baseChange b).obj G'
  -- The difference map `g ↦ φ₁(g) φ₂(g)⁻¹`.
  let δ : GR.X ⟶ GR'.X := φ₁.hom.hom * φ₂.hom.hom⁻¹
  have hδ : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ GR.X),
      x ≫ δ = (x ≫ φ₁.hom.hom) * (x ≫ φ₂.hom.hom)⁻¹ := by
    intro T x
    simp only [δ, MonObj.comp_mul, GrpObj.comp_inv]
  have hcoset : ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ GR.X),
      g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier T → g ≫ δ = h ≫ δ := by
    intro T g h hgh
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hgh
    have hh : h = g * (y ≫ j.hom.hom) := by rw [hy, mul_inv_cancel_left]
    have hj : y ≫ j.hom.hom ≫ φ₁.hom.hom = y ≫ j.hom.hom ≫ φ₂.hom.hom := by
      rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hφ]
    rw [hδ, hδ, hh, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, hj]
    group
  have : Flat Q₁.projection.left := by
    have := Q₁.smooth_projection
    infer_instance
  have : Surjective Q₁.projection.left := Q₁.surjective_projection
  have : QuasiCompact Q₁.projection.left := Q₁.quasiCompact_projection
  obtain ⟨ρ, hρ⟩ := ParabolicQuotient.exists_factor j Q₁.projection δ
    (fun T g h hgh => (Q₁.fibers T g h).mp hgh) hcoset
  -- The underlying scheme maps, written on the actual fibre products.
  let P : pullback G.X.hom b ⟶ pullback Q.hom b := Q₁.projection.left
  let r : pullback Q.hom b ⟶ pullback G'.X.hom b := ρ.left
  let d : pullback G.X.hom b ⟶ pullback G'.X.hom b := δ.left
  have hPr : P ≫ r = d := congrArg (fun x => CommaMorphism.left x) hρ
  -- Global functions of `Q_R` are those of `Spec R ×_k Spec Γ(Q)`.
  let hm' : pullback b Q.hom ⟶ pullback b (algebraSchemeMap Q.hom) :=
    schemeMap Q.hom (Over.mk b)
  have hm1 : hm' ≫ pullback.fst b (algebraSchemeMap Q.hom) = pullback.fst b Q.hom :=
    schemeMap_fst Q.hom (Over.mk b)
  have hm2 : hm' ≫ pullback.snd b (algebraSchemeMap Q.hom) =
      pullback.snd b Q.hom ≫ Q.left.toSpecΓ :=
    schemeMap_snd Q.hom (Over.mk b)
  have : IsIso hm'.appTop := isIso_schemeMap_appTop Q.hom (Over.mk b)
  let hmap : pullback Q.hom b ⟶ pullback b (algebraSchemeMap Q.hom) :=
    (pullbackSymmetry Q.hom b).hom ≫ hm'
  have : IsIso (pullbackSymmetry Q.hom b).hom.appTop :=
    ⟨⟨(pullbackSymmetry Q.hom b).inv.appTop, by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop], by
      rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]⟩⟩
  have : IsIso hmap.appTop := by
    change IsIso ((pullbackSymmetry Q.hom b).hom ≫ hm').appTop
    rw [Scheme.Hom.comp_appTop]
    infer_instance
  have hmap_fst : hmap ≫ pullback.fst b (algebraSchemeMap Q.hom) = pullback.snd Q.hom b := by
    change ((pullbackSymmetry Q.hom b).hom ≫ hm') ≫ _ = _
    rw [Category.assoc, hm1, pullbackSymmetry_hom_comp_fst]
  have hmap_snd : hmap ≫ pullback.snd b (algebraSchemeMap Q.hom) =
      pullback.fst Q.hom b ≫ Q.left.toSpecΓ := by
    change ((pullbackSymmetry Q.hom b).hom ≫ hm') ≫ _ = _
    rw [Category.assoc, hm2, pullbackSymmetry_hom_comp_snd_assoc]
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : IsAffine (pullback G'.X.hom b) := isAffine_of_isAffineHom (pullback.snd G'.X.hom b)
  obtain ⟨τ, hτ⟩ := exists_factor_of_isIso_appTop hmap r
  -- The composite `G_R → Q_R → Spec R ×_k Spec Γ(Q)` only depends on the point of `Spec R`.
  let e : Spec (CommRingCat.of k) ⟶ G.X.left := η[G.X].left
  have he : e ≫ G.X.hom = 𝟙 _ := Over.w η[G.X]
  have : IsIntegral G.X.left := CoverPreimage.isIntegral_of_smooth_connected G
  have hconst := toSpecΓ_comp_eq G.X.hom e he Q.hom q.left (Over.w q)
  have hc : (e ≫ q.left ≫ Q.left.toSpecΓ) ≫ algebraSchemeMap Q.hom = 𝟙 _ := by
    rw [Category.assoc, Category.assoc, toSpecΓ_over, Over.w q, he]
  let s : Spec (CommRingCat.of R) ⟶ pullback b (algebraSchemeMap Q.hom) :=
    pullback.lift (𝟙 _) (b ≫ e ≫ q.left ≫ Q.left.toSpecΓ)
      (by rw [Category.assoc, hc, Category.comp_id, Category.id_comp])
  have hs1 : s ≫ pullback.fst b (algebraSchemeMap Q.hom) = 𝟙 _ := pullback.lift_fst _ _ _
  have hs2 : s ≫ pullback.snd b (algebraSchemeMap Q.hom) =
      b ≫ e ≫ q.left ≫ Q.left.toSpecΓ := pullback.lift_snd _ _ _
  have hpf : P ≫ pullback.fst Q.hom b = pullback.fst G.X.hom b ≫ q.left :=
    Q₀.baseChange_projection_fst b
  have hps : P ≫ pullback.snd Q.hom b = pullback.snd G.X.hom b :=
    Over.w Q₁.projection
  have hfac : P ≫ hmap = pullback.snd G.X.hom b ≫ s := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmap_fst, hps, Category.assoc, hs1, Category.comp_id]
    · rw [Category.assoc, hmap_snd, ← Category.assoc, hpf, Category.assoc, hconst,
        Category.assoc, hs2, ← Category.assoc (pullback.fst G.X.hom b),
        pullback.condition, Category.assoc]
  -- Hence `δ` is constant, equal to its value at the unit.
  have hδl : d = pullback.snd G.X.hom b ≫ s ≫ τ := by
    rw [← hPr, ← hτ, ← Category.assoc, hfac, Category.assoc]
  have hη : η[GR.X] ≫ δ = η[GR'.X] := by
    rw [hδ, IsMonHom.one_hom φ₁.hom.hom, IsMonHom.one_hom φ₂.hom.hom, mul_inv_cancel,
      MonObj.one_eq_one]
  let u : Spec (CommRingCat.of R) ⟶ pullback G.X.hom b := η[GR.X].left
  let u' : Spec (CommRingCat.of R) ⟶ pullback G'.X.hom b := η[GR'.X].left
  have hσ : s ≫ τ = u' := by
    have h1 : u ≫ d = u' := congrArg (fun x => CommaMorphism.left x) hη
    have h2 : u ≫ pullback.snd G.X.hom b = 𝟙 _ := Over.w η[GR.X]
    rw [hδl, ← Category.assoc, h2, Category.id_comp] at h1
    exact h1
  have hδ1 : δ = 1 := by
    rw [Hom.one_def]
    ext1
    change d = (CartesianMonoidalCategory.toUnit GR.X).left ≫ u'
    rw [hδl, hσ, Over.toUnit_left]
    rfl
  apply Grp.hom_ext
  exact mul_inv_eq_one.mp hδ1

end Langlands.GroupScheme
