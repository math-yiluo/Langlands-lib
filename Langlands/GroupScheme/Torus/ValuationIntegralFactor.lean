import Langlands.GroupScheme.HomScheme.ConjugateFamilyFactorization
import Langlands.GroupScheme.GenericGroupMonoLift
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.TorusGraphGroupQuotient
import Mathlib.RingTheory.Valuation.LocalSubring

/-! # The integral closed factor of a generically conjugate torus family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G D Q L : GroupScheme S} {M : Over S} {K : GroupScheme M.left}
variable {Ω : Type u} [Field Ω] (A : ValuationSubring Ω)

/-- A closed factorization, over a valuation ring `A`, of the evaluated torus family
through the base change of an intermediate group `Q ⟶ L`. It retains the comparison of
the generic fibre of the evaluated torus with the generic fibre of `D`. -/
structure IntegralFactor (D : GroupScheme S) (m : Q ⟶ L) (j : K ⟶ (baseChange M.hom).obj L)
    (a : Spec (CommRingCat.of A) ⟶ S) (b : Over.mk a ⟶ M) where
  factor : (baseChange b.left).obj K ⟶ (baseChange a).obj Q
  fac : factor ≫ (baseChange a).map m = familyHom j b
  isClosedSubgroup_factor : IsClosedSubgroup factor
  genericIso : (baseChange (Spec.algebraMap A Ω)).obj ((baseChange b.left).obj K) ≅
    (baseChange (Spec.algebraMap A Ω)).obj ((baseChange a).obj D)

/-- If the evaluated torus family is the conjugate of `D` by the image of a point of `G`
over the fraction field, its generic factorization through `Q` extends to a closed
factorization over the valuation ring. -/
def integralFactor (q : G ⟶ Q) (d : D ⟶ Q) (m : Q ⟶ L) [Mono m.hom.hom.left]
    [QuasiCompact Q.X.hom] [LocallyOfFiniteType Q.X.hom] [QuasiSeparated L.X.hom]
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (hd : IsClosedSubgroup (d ≫ m)) (f : G.X ⟶ M)
    (hf : evaluate j f = range (conjugateFamily (d ≫ m) (q ≫ m).hom.hom))
    (a : Spec (CommRingCat.of A) ⟶ S) (b : Over.mk a ⟶ M)
    (g : Over.mk (Spec.algebraMap A Ω ≫ a) ⟶ G.X)
    (hg : g ≫ f = (Over.homMk (Spec.algebraMap A Ω) rfl :
      Over.mk (Spec.algebraMap A Ω ≫ a) ⟶ Over.mk a) ≫ b) :
    IntegralFactor A D m j a b := by
  let s := Spec.algebraMap A Ω
  let r := restrictedFamilyFactorization q d m j hj hd f hf b s g hg
  let B := (baseChange b.left).obj K
  let H := (baseChange a).obj Q
  let L' := (baseChange a).obj L
  let i : H ⟶ L' := (baseChange a).map m
  let e : B ⟶ L' := familyHom j b
  have hB : RelativeTorus.IsTorus B := hK.baseChange b.left
  let : Smooth B.X.hom := hB.smooth
  let : GeometricallyConnected B.X.hom := hB.geometricallyConnected
  let : Mono m.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom.left := inferInstanceAs (Mono ((Over.pullback a).map m.hom.hom).left)
  let : QuasiCompact H.X.hom := inferInstanceAs (QuasiCompact (pullback.snd Q.X.hom a))
  let : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Q.X.hom a))
  let : QuasiSeparated L'.X.hom := inferInstanceAs (QuasiSeparated (pullback.snd L.X.hom a))
  have hiw : i.hom.hom.left ≫ L'.X.hom = H.X.hom := Over.w i.hom.hom
  let : QuasiCompact i.hom.hom.left := by
    have : QuasiCompact (i.hom.hom.left ≫ L'.X.hom) := by rw [hiw]; infer_instance
    exact QuasiCompact.of_comp _ L'.X.hom
  let : LocallyOfFiniteType i.hom.hom.left := by
    have : LocallyOfFiniteType (i.hom.hom.left ≫ L'.X.hom) := by rw [hiw]; infer_instance
    exact locallyOfFiniteType_of_comp _ L'.X.hom
  have hnat {X Y : GroupScheme (Spec (CommRingCat.of A))} (φ : X ⟶ Y) :
      ((baseChange s).map φ).hom.hom.left ≫ pullback.fst Y.X.hom s =
        pullback.fst X.X.hom s ≫ φ.hom.hom.left :=
    pullback.lift_fst _ _ _
  let x : pullback B.X.hom s ⟶ H.X.left := r.factor.hom.hom.left ≫ pullback.fst H.X.hom s
  have hfac : r.factor.hom.hom.left ≫ ((baseChange s).map i).hom.hom.left =
      ((baseChange s).map e).hom.hom.left :=
    congrArg (fun φ => φ.hom.hom.left) r.fac
  have hx : x ≫ i.hom.hom.left = pullback.fst B.X.hom s ≫ e.hom.hom.left := by
    rw [Category.assoc, ← hnat i, ← Category.assoc, hfac, hnat e]
  let c := genericGroupMonoLift (CommRingCat.of A) (K := Ω) i e x hx
  have hc : IsClosedSubgroup c.val := by
    have hcl : IsClosedImmersion (c.val.hom.hom.left ≫ i.hom.hom.left) := by
      change IsClosedImmersion (c.val ≫ i).hom.hom.left
      rw [c.property]
      exact isClosedSubgroup_familyHom j hj b
    exact IsClosedImmersion.of_comp c.val.hom.hom.left i.hom.hom.left
  exact ⟨c.val, c.property, hc, r.sourceIso⟩

/-- The integral factor for the original points of the valuative criterion: a point
`b` of `M` over the valuation ring whose restriction to the fraction field is the image of
a point `g` of `G`. -/
def integralFactorOfPoints (q : G ⟶ Q) (d : D ⟶ Q) (m : Q ⟶ L) [Mono m.hom.hom.left]
    [QuasiCompact Q.X.hom] [LocallyOfFiniteType Q.X.hom] [QuasiSeparated L.X.hom]
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (hd : IsClosedSubgroup (d ≫ m)) (f : G.X ⟶ M)
    (hf : evaluate j f = range (conjugateFamily (d ≫ m) (q ≫ m).hom.hom))
    (g : Spec (CommRingCat.of Ω) ⟶ G.X.left) (b : Spec (CommRingCat.of A) ⟶ M.left)
    (hgb : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ b = g ≫ f.left) :
    IntegralFactor A D m j (b ≫ M.hom) (Over.homMk b rfl) := by
  let s := Spec.algebraMap A Ω
  let g₀ : Over.mk (s ≫ b ≫ M.hom) ⟶ G.X := Over.homMk g (by
    change g ≫ G.X.hom = s ≫ b ≫ M.hom
    rw [← Over.w f, ← Category.assoc, ← hgb, Category.assoc])
  refine integralFactor A q d m j hj hK hd f hf (b ≫ M.hom) (Over.homMk b rfl) g₀ ?_
  exact Over.OverMorphism.ext hgb.symm

end Langlands.GroupScheme.TorusSubgroupModuli

namespace Langlands.GroupScheme.TorusGraphQuotient.GroupFactorization

open TorusSubgroupModuli SubgroupFunctor

variable {S : Scheme.{u}} {G L : GroupScheme S} {D : CommGroupScheme S} {M : Over S}
  {K : GroupScheme M.left}
variable {Ω : Type u} [Field Ω] (A : ValuationSubring Ω)

/-- The integral factor through the quotient of a graph factorization `F` of `ρ` and `e`,
for the conjugacy family of the closed image torus `e`. -/
def integralFactor {ρ : G ⟶ L} {e : D.toGrp ⟶ L} (F : GroupFactorization ρ e)
    [QuasiSeparated L.X.hom] (he : IsClosedSubgroup e)
    (j : K ⟶ (baseChange M.hom).obj L) (hj : IsClosedSubgroup j)
    (hK : RelativeTorus.IsTorus K) (f : G.X ⟶ M)
    (hf : evaluate j f = range (conjugateFamily e ρ.hom.hom))
    (g : Spec (CommRingCat.of Ω) ⟶ G.X.left) (b : Spec (CommRingCat.of A) ⟶ M.left)
    (hgb : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ b = g ≫ f.left) :
    IntegralFactor A D.toGrp F.embedding j (b ≫ M.hom) (Over.homMk b rfl) :=
  let : Mono F.embedding.hom.hom.left := F.mono_embedding
  let : QuasiCompact F.quotient.X.hom := F.quasiCompact_quotient
  let : Smooth F.quotient.X.hom := F.smooth_quotient
  integralFactorOfPoints A F.projection F.torus F.embedding j hj hK
    (by rw [F.torus_fac]; exact he) f (by rw [F.torus_fac, F.projection_fac]; exact hf) g b hgb

end Langlands.GroupScheme.TorusGraphQuotient.GroupFactorization
