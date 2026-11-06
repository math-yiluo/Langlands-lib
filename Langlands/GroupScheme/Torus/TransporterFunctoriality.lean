import Langlands.GroupScheme.Torus.TwistedTransporter
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Functoriality of the actual all-test transporter relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H K G G' : GroupScheme S}
  {i₁ i₂ : H ⟶ G} {T U : Over S} {g : T ⟶ G.X}

/-- Restricting the specified transporter point preserves its relation on
every further test scheme. -/
theorem IsTransporter.restrict (hg : IsTransporter i₁ i₂ g) (a : U ⟶ T) :
    IsTransporter i₁ i₂ (a ≫ g) := by
  intro V b h
  simpa only [Category.assoc] using hg V (b ≫ a) h

/-- Precomposing the two homomorphisms preserves the actual transporter point. -/
theorem IsTransporter.precomp (hg : IsTransporter i₁ i₂ g) (f : K ⟶ H) :
    IsTransporter (f ≫ i₁) (f ≫ i₂) g := by
  intro V a h
  simpa only [Grp.comp_hom_hom, Category.assoc] using hg V a (h ≫ f.hom.hom)

/-- A group homomorphism carries a transporter point to a transporter point. -/
theorem IsTransporter.map (hg : IsTransporter i₁ i₂ g) (j : G ⟶ G') :
    IsTransporter (i₁ ≫ j) (i₂ ≫ j) (g ≫ j.hom.hom) := by
  intro V a h
  simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using
    congrArg (fun x => x ≫ j.hom.hom) (hg V a h)

/-- A monomorphic target homomorphism reflects the actual transporter equation. -/
theorem IsTransporter.of_comp (j : G ⟶ G') [Mono j.hom.hom]
    (hg : IsTransporter (i₁ ≫ j) (i₂ ≫ j) (g ≫ j.hom.hom)) :
    IsTransporter i₁ i₂ g := by
  intro V a h
  apply (cancel_mono j.hom.hom).mp
  simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using hg V a h

/-- Transporter equations are unchanged by a monomorphic ambient inclusion.
This permits their reflection into an actual identity component. -/
theorem isTransporter_comp_iff (j : G ⟶ G') [Mono j.hom.hom] :
    IsTransporter (i₁ ≫ j) (i₂ ≫ j) (g ≫ j.hom.hom) ↔
      IsTransporter i₁ i₂ g :=
  ⟨IsTransporter.of_comp j, fun hg => hg.map j⟩

variable {S' : Scheme.{u}} (b : S' ⟶ S)

/-- The actual pullback point associated to a specified refinement of the
original transporter point. -/
def baseChangeTransporterPoint {V : Over S'} (a : (Over.map b).obj V ⟶ T) :
    V ⟶ ((baseChange b).obj G).X :=
  (baseChangePointsEquiv b G V).symm (a ≫ g)

@[simp] theorem baseChangeTransporterPoint_recovers {V : Over S'}
    (a : (Over.map b).obj V ⟶ T) :
    baseChangePointsEquiv b G V (baseChangeTransporterPoint (g := g) b a) = a ≫ g :=
  (baseChangePointsEquiv b G V).apply_symm_apply _

/-- Pullback preserves the all-test transporter relation whenever the new
point recovers a refinement of the old point under the actual pullback-point
equivalence. No flatness or affineness is assumed. -/
theorem IsTransporter.baseChange (hg : IsTransporter i₁ i₂ g)
    {V : Over S'} (a : (Over.map b).obj V ⟶ T)
    (g' : V ⟶ ((baseChange b).obj G).X)
    (he : baseChangePointsEquiv b G V g' = a ≫ g) :
    IsTransporter ((baseChange b).map i₁) ((baseChange b).map i₂) g' := by
  intro W c h
  apply (baseChangePointsEquiv b G W).injective
  rw [map_mul, map_mul, baseChangePointsEquiv_comp b i₁ W h,
    baseChangePointsEquiv_comp b i₂ W h, baseChangePointsEquiv_naturality, he]
  simpa only [Category.assoc] using
    hg ((Over.map b).obj W) ((Over.map b).map c ≫ a)
      (baseChangePointsEquiv b H W h)

/-- The constructed actual pullback point is a transporter for the pulled-back
homomorphisms on all refinements. -/
theorem IsTransporter.baseChange_point (hg : IsTransporter i₁ i₂ g)
    {V : Over S'} (a : (Over.map b).obj V ⟶ T) :
    IsTransporter ((GroupScheme.baseChange b).map i₁) ((GroupScheme.baseChange b).map i₂)
      (baseChangeTransporterPoint (g := g) b a) :=
  hg.baseChange b a _ (baseChangeTransporterPoint_recovers b a)

end PointwiseSchemeAction

section NormalizingPoint

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}

/-- An actual normalizing point is the actual all-test transporter for its
specified torus automorphism, with the same orientation as the rank-one criterion. -/
theorem IsNormalizingPoint.isTransporter (hn : IsNormalizingPoint i n σ) :
    PointwiseSchemeAction.IsTransporter (CommGroupScheme.groupHom σ.hom ≫ i) i n := by
  intro V a t
  have he := congrArg (fun f : T.toGrp ⟶ G => t ≫ f.hom.hom) hn
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom] at he
  have hc : G.constantPoint n V = a ≫ n := by
    unfold GroupScheme.constantPoint
    congr 1
    apply Over.OverMorphism.ext
    change V.hom = a.left
    have ha := Over.w a
    change a.left ≫ 𝟙 S = V.hom at ha
    exact ha.symm.trans (Category.comp_id _)
  rw [hc] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

end NormalizingPoint

end Langlands.GroupScheme
