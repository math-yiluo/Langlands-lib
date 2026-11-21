import Langlands.Geometry.FormalGroup.PDivisibleRationalBaseChange
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Identity and composition comparisons for pullback of actual towers -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.PDivisibleGroup

open GroupScheme.HomScheme

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {p : ℕ} [Fact p.Prime]

private theorem specBase_self : specBase R R = 𝟙 (Spec (CommRingCat.of R)) := by
  rw [specBase, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

private def levelBaseChangeIdNatIso :
    CommGroupScheme.baseChange (specBase R R) ≅ 𝟭 (CommGroupScheme (Spec (CommRingCat.of R))) :=
  eqToIso (congrArg CommGroupScheme.baseChange (specBase_self (R := R))) ≪≫
  NatIso.ofComponents (fun G => GroupScheme.CommGroupScheme.isoOfGroupIso (GroupScheme.baseChangeIdIso G.toGrp))
    (by
      intro G H f
      exact congrArg Additive.ofMul
        ((Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso).hom.naturality f.toMul))

/-- A natural isomorphism of the actual inclusion diagrams gives an isomorphism of towers. -/
def isoOfInclusionDiagrams {G H : PDivisibleGroup (CommRingCat.of R) p}
    (e : G.inclusions ≅ H.inclusions) : G ≅ H where
  hom := Hom.ofNaturalTransformation e.hom
  inv := Hom.ofNaturalTransformation e.inv
  hom_inv_id := Hom.ext fun n => (e.app n).hom_inv_id
  inv_hom_id := Hom.ext fun n => (e.app n).inv_hom_id

/-- The pullback along the identity algebra map is isomorphic to the original tower. -/
def baseChangeIdIso (G : PDivisibleGroup (CommRingCat.of R) p) :
    (baseChangeFunctor R R p).obj G ≅ G := by
  let H := (baseChangeFunctor R R p).obj G
  let e := levelBaseChangeIdNatIso (R := R)
  let e' : H.inclusions ≅ G.inclusions := NatIso.ofComponents
    (fun n => e.app (G.inclusions.obj n)) (fun i => e.hom.naturality (G.inclusions.map i))
  exact isoOfInclusionDiagrams (G := H) (H := G) e'

/-- The identity pullback comparison is natural in the actual tower. -/
def baseChangeIdNatIso (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] :
    baseChangeFunctor R R p ≅ 𝟭 (PDivisibleGroup (CommRingCat.of R) p) :=
  NatIso.ofComponents baseChangeIdIso (by
    intro G H f
    apply Hom.ext
    intro n
    exact (levelBaseChangeIdNatIso (R := R)).hom.naturality (f.app n))

section Composition

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

private theorem specBase_comp : specBase R T = specBase S T ≫ specBase R S := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

private def levelBaseChangeCompNatIso :
    CommGroupScheme.baseChange (specBase R T) ≅
      CommGroupScheme.baseChange (specBase R S) ⋙ CommGroupScheme.baseChange (specBase S T) :=
  eqToIso (congrArg CommGroupScheme.baseChange (specBase_comp (R := R) (S := S) (T := T))) ≪≫
  NatIso.ofComponents (fun G => GroupScheme.CommGroupScheme.isoOfGroupIso
    (GroupScheme.baseChangeCompIso (specBase R S) (specBase S T) G.toGrp))
    (by
      intro G H f
      exact congrArg Additive.ofMul
        ((Functor.mapGrpNatIso (Over.pullbackComp (specBase S T) (specBase R S)) ≪≫
          Functor.mapGrpCompIso).hom.naturality f.toMul))

/-- A direct pullback is isomorphic to the successive pullback of the actual tower. -/
def baseChangeCompIso (G : PDivisibleGroup (CommRingCat.of R) p) :
    (baseChangeFunctor R T p).obj G ≅ (baseChangeFunctor R S p ⋙ baseChangeFunctor S T p).obj G := by
  let H₁ := (baseChangeFunctor R T p).obj G
  let H₂ := (baseChangeFunctor R S p ⋙ baseChangeFunctor S T p).obj G
  let e := levelBaseChangeCompNatIso (R := R) (S := S) (T := T)
  let e' : H₁.inclusions ≅ H₂.inclusions := NatIso.ofComponents
    (fun n => e.app (G.inclusions.obj n)) (fun i => e.hom.naturality (G.inclusions.map i))
  exact isoOfInclusionDiagrams (G := H₁) (H := H₂) e'

/-- The successive pullback comparison is natural in the actual tower. -/
def baseChangeCompNatIso (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (p : ℕ) [Fact p.Prime] :
    baseChangeFunctor R T p ≅ baseChangeFunctor R S p ⋙ baseChangeFunctor S T p :=
  NatIso.ofComponents (baseChangeCompIso (S := S)) (by
    intro G H f
    apply Hom.ext
    intro n
    exact (levelBaseChangeCompNatIso (R := R) (S := S) (T := T)).hom.naturality (f.app n))

end Composition

/-- Identity pullback commutes with actual rational tower morphisms. -/
def rationalBaseChangeIdNatIso (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] :
    rationalBaseChangeFunctor R R p ≅ 𝟭 (RationalCategory (CommRingCat.of R) p) :=
  NatIso.ofComponents (fun G => RationalCategory.inclusion.mapIso ((baseChangeIdNatIso R p).app G.val))
    (by
      intro G H f
      let e := baseChangeIdNatIso R p
      change RationalHom.comp (RationalHom.baseChangeMap (S := R) f) (RationalHom.ofHom (e.app H.val).hom) =
        RationalHom.comp (RationalHom.ofHom (e.app G.val).hom) f
      induction f using TensorProduct.inductionOn with
      | tmul a g =>
        simp only [RationalHom.baseChangeMap_tmul, RationalHom.ofHom_apply,
          RationalHom.comp_tmul, mul_one, one_mul]
        exact congrArg (a ⊗ₜ[ℤ_[p]] ·) (e.hom.naturality g)
      | add f g hf hg => simp only [map_add, RationalHom.add_comp, RationalHom.comp_add, hf, hg])

/-- Direct and successive pullback agree naturally on the actual rational category. -/
def rationalBaseChangeCompNatIso (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (p : ℕ) [Fact p.Prime] :
    rationalBaseChangeFunctor R T p ≅ rationalBaseChangeFunctor R S p ⋙ rationalBaseChangeFunctor S T p :=
  NatIso.ofComponents (fun G => RationalCategory.inclusion.mapIso
    ((baseChangeCompNatIso R S T p).app G.val))
    (by
      intro G H f
      let e := baseChangeCompNatIso R S T p
      change RationalHom.comp (RationalHom.baseChangeMap (S := T) f) (RationalHom.ofHom (e.app H.val).hom) =
        RationalHom.comp (RationalHom.ofHom (e.app G.val).hom)
          (RationalHom.baseChangeMap (S := T) (RationalHom.baseChangeMap (S := S) f))
      induction f using TensorProduct.inductionOn with
      | tmul a g =>
        simp only [RationalHom.baseChangeMap_tmul, RationalHom.ofHom_apply,
          RationalHom.comp_tmul, mul_one, one_mul]
        exact congrArg (a ⊗ₜ[ℤ_[p]] ·) (e.hom.naturality g)
      | add f g hf hg => simp only [map_add, RationalHom.add_comp, RationalHom.comp_add, hf, hg])

end Langlands.PDivisibleGroup
