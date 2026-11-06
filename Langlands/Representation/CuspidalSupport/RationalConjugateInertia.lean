import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.GroupScheme.ConjugacyComposition

/-! # Inertia transport along actual algebraic conjugacies -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G H K L : GroupScheme (Spec (CommRingCat.of F))}

section PointTransport

variable [IsAffine H.X.left] [IsAffine K.X.left] [IsAffine L.X.left]

local instance (M : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left] :
    TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X

/-- An actual algebraic group isomorphism gives the canonical point homeomorphism. -/
def rationalPointIso (e : H ≅ K) : GroupScheme.rationalPoints H ≃ₜ* GroupScheme.rationalPoints K where
  toFun := GroupScheme.rationalPoints.map e.hom
  invFun := GroupScheme.rationalPoints.map e.inv
  left_inv x := by
    change (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv x := by
    change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_mul' := (GroupScheme.rationalPoints.map e.hom).map_mul
  continuous_toFun := (rationalContinuousPointsMap e.hom).continuous
  continuous_invFun := (rationalContinuousPointsMap e.inv).continuous

@[simp] theorem rationalPointIso_apply (e : H ≅ K) (x : GroupScheme.rationalPoints H) :
    rationalPointIso e x = GroupScheme.rationalPoints.map e.hom x := rfl

@[simp] theorem rationalPointIso_refl_apply (x : GroupScheme.rationalPoints H) :
    rationalPointIso (Iso.refl H) x = x := by
  change x ≫ (𝟙 H.X) = x
  rw [Category.comp_id]

@[simp] theorem rationalPointIso_trans_apply (e : H ≅ K) (f : K ≅ L)
    (x : GroupScheme.rationalPoints H) :
    rationalPointIso (e ≪≫ f) x = rationalPointIso f (rationalPointIso e x) := by
  change x ≫ (e.hom ≫ f.hom).hom.hom = (x ≫ e.hom.hom.hom) ≫ f.hom.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

@[simp] theorem rationalPointIso_symm_apply_apply (e : H ≅ K)
    (x : GroupScheme.rationalPoints H) :
    rationalPointIso e.symm (rationalPointIso e x) = x :=
  (rationalPointIso e).symm_apply_apply x

/-- Pullback retains the actual representation carrier. -/
abbrev rationalIsoPullback (e : H ≅ K)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)) :
    SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H) :=
  SmoothRep.pullback (rationalPointIso e) A

/-- Pullback by the identity is the identity through its actual linear map. -/
def rationalIsoPullbackReflIso
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    rationalIsoPullback (Iso.refl H) A ≅ A :=
  SmoothRep.mkIso (equivOfRepresentationEq (by
    ext x v
    change A.representation (rationalPointIso (Iso.refl H) x) v = A.representation x v
    rw [rationalPointIso_refl_apply]))

/-- Successive algebraic pullbacks compose through the identity on carriers. -/
def rationalIsoPullbackTransIso (e : H ≅ K) (f : K ≅ L)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints L)) :
    rationalIsoPullback e (rationalIsoPullback f A) ≅ rationalIsoPullback (e ≪≫ f) A :=
  SmoothRep.mkIso (equivOfRepresentationEq (by
    ext x v
    change A.representation (rationalPointIso f (rationalPointIso e x)) v =
      A.representation (rationalPointIso (e ≪≫ f) x) v
    rw [rationalPointIso_trans_apply]))

/-- An inverse algebraic pullback cancels the original one. -/
def rationalIsoPullbackCancelIso (e : H ≅ K)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H)) :
    rationalIsoPullback e (rationalIsoPullback e.symm A) ≅ A :=
  SmoothRep.mkIso (equivOfRepresentationEq (by
    ext x v
    change A.representation (rationalPointIso e.symm (rationalPointIso e x)) v =
      A.representation x v
    rw [rationalPointIso_symm_apply_apply]))

variable [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType K.X.hom]

/-- Algebraic pullback transports the full rational unramified character,
not a chosen subfamily of norm coordinates. -/
def rationalIsoPullbackTwistIso (e : H ≅ K)
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters K ψ).toMul))
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)) :
    rationalIsoPullback e (rationalUnramifiedTwist K χ A) ≅
      rationalUnramifiedTwist H (rationalUnramifiedCharacterRestrict e.hom χ)
        (rationalIsoPullback e A) :=
  SmoothRep.mkIso (equivOfRepresentationEq (by rfl))

/-- Same-Levi inertia equivalence is preserved by actual algebraic transport. -/
theorem IsRationalInertiaRelated.rationalIsoPullback (e : H ≅ K)
    {A B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)}
    (h : IsRationalInertiaRelated K A B) :
    IsRationalInertiaRelated H (rationalIsoPullback e A) (rationalIsoPullback e B) := by
  obtain ⟨χ, ⟨hχ⟩⟩ := h
  exact ⟨rationalUnramifiedCharacterRestrict e.hom χ,
    ⟨(SmoothRep.pullbackFunctor (rationalPointIso e)).mapIso hχ ≪≫
      rationalIsoPullbackTwistIso e χ A⟩⟩

/-- Source-side and target-side formulations of the transported inertia orbit agree. -/
theorem rationalInertiaRelated_pullback_iff (e : H ≅ K)
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints H))
    (B : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints K)) :
    IsRationalInertiaRelated H A (rationalIsoPullback e B) ↔
      IsRationalInertiaRelated K (rationalIsoPullback e.symm A) B := by
  constructor
  · intro h
    exact (h.rationalIsoPullback e.symm).trans
      (.of_iso (rationalIsoPullbackCancelIso e.symm B))
  · intro h
    exact (IsRationalInertiaRelated.of_iso (rationalIsoPullbackCancelIso e A).symm).trans
      (h.rationalIsoPullback e)

end PointTransport

/-- Conjugacy is an actual ambient rational point and an algebraic isomorphism
whose two embeddings agree with its inner automorphism on every test scheme. -/
structure RationalLeviConjugacy (j : H ⟶ G) (k : K ⟶ G) where
  point : GroupScheme.rationalPoints G
  iso : H ≅ K
  commutes : j ≫ (G.innerIso point).hom = iso.hom ≫ k

namespace RationalLeviConjugacy

variable {j : H ⟶ G} {k : K ⟶ G} {l : L ⟶ G}

/-- Identity conjugation. -/
def refl (j : H ⟶ G) : RationalLeviConjugacy j j where
  point := 1
  iso := Iso.refl H
  commutes := by rw [G.innerIso_one_hom]; simp

/-- Invert the actual point and the algebraic Levi isomorphism. -/
def symm (c : RationalLeviConjugacy j k) : RationalLeviConjugacy k j where
  point := c.point⁻¹
  iso := c.iso.symm
  commutes := by
    have hk : k ≫ (G.innerIso (1 : GroupScheme.rationalPoints G)).hom =
        (Iso.refl K).hom ≫ k := by rw [G.innerIso_one_hom]; simp
    simpa using GroupScheme.comp_innerIso_hom_of_common_target hk c.commutes

/-- Compose the algebraic isomorphisms and the actual ambient conjugating points. -/
def trans (c : RationalLeviConjugacy j k) (d : RationalLeviConjugacy k l) :
    RationalLeviConjugacy j l where
  point := d.point * c.point
  iso := c.iso ≪≫ d.iso
  commutes := by
    rw [G.innerIso_mul_hom, reassoc_of% c.commutes, d.commutes,
      Iso.trans_hom, Category.assoc]

end RationalLeviConjugacy

end Langlands.CuspidalSupport
