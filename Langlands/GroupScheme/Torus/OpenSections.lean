import Langlands.GroupScheme.Torus.LocalCocycle
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeLocalSections

/-! # Local sections of quotients by split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}
  {ξ : Cocycle G U} {y : S}

/-- A local trivialization transports back through an isomorphism of its value group. -/
def LocalTrivialization.of_map (e : G ≅ H)
    (L : (ξ.map e.hom).LocalTrivialization y) : ξ.LocalTrivialization y where
  openSet := L.openSet
  mem_openSet := L.mem_openSet
  cochain := L.cochain ≫ e.inv.hom.hom
  coboundary a b := by
    have hcomp : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
      ((Grp.forget (Over S)).mapIso e).hom_inv_id
    have h := congrArg (fun x => x ≫ e.inv.hom.hom) (L.coboundary a b)
    change (ξ.toFun _ _ ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = _ at h
    rw [Category.assoc, hcomp, Category.comp_id, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [Category.assoc] using h

/-- Cocycles of any split torus are locally trivial on affine faithfully flat covers. -/
theorem nonempty_localTrivialization_of_isSplitTorus
    (hG : IsSplitTorus G) [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle G U) (y : S) : Nonempty (ξ.LocalTrivialization y) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact ⟨((ξ.map e.hom).localTrivialization y).of_map e⟩

end Cocycle

namespace SplitTorusQuotient

open SplitUnipotentAffineTorsor

variable {S : Scheme.{u}} {K H C : GroupScheme S}
  (j : K ⟶ H) (q : H ⟶ C) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

/-- An actual section of the underlying scheme map on a neighbourhood of a point. -/
structure LocalSection (y : C.X.left) where
  openSet : C.X.left.Opens
  mem_openSet : y ∈ openSet
  sectionMap : openSet.toScheme ⟶ H.X.left
  section_fac : sectionMap ≫ q.hom.hom.left = openSet.ι

include hjq in
/-- A quotient with split-torus kernel has an actual scheme section on a neighbourhood
of every point of its target. -/
theorem exists_localSection [IsAffineHom q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hK : IsSplitTorus K) (y : C.X.left) :
    ∃ (W : C.X.left.Opens), y ∈ W ∧
      ∃ s : W.toScheme ⟶ H.X.left, s ≫ q.hom.hom.left = W.ι := by
  let b := C.X.hom
  let U' : Over C.X.left := Over.mk q.hom.hom.left
  have : IsAffineHom U'.hom := ‹IsAffineHom q.hom.hom.left›
  have : Flat U'.hom := ‹Flat q.hom.hom.left›
  have : Surjective U'.hom := ‹Surjective q.hom.hom.left›
  let e : (Over.map b).obj U' ⟶ H.X :=
    Over.homMk (𝟙 H.X.left) ((Category.id_comp _).trans (Over.w q.hom.hom).symm)
  let F : U' ⟶ ((GroupScheme.baseChange b).obj H).X := (baseChangePointsEquiv b H U').symm e
  let q' := ((GroupScheme.baseChange b).map q).hom.hom
  let j' := ((GroupScheme.baseChange b).map j).hom.hom
  have hFq : ∀ {Z : Over C.X.left} (a₁ a₂ : Z ⟶ U'), a₁ ≫ F ≫ q' = a₂ ≫ F ≫ q' := by
    intro Z a₁ a₂
    apply (baseChangePointsEquiv b C Z).injective
    rw [← Category.assoc, ← Category.assoc, baseChangePointsEquiv_comp,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_naturality,
      baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change a₁.left ≫ 𝟙 _ ≫ q.hom.hom.left = a₂.left ≫ 𝟙 _ ≫ q.hom.hom.left
    exact (Over.w a₁).trans (Over.w a₂).symm
  have hval : ∀ {Z : Over C.X.left} (a₁ a₂ : Z ⟶ U'),
      ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
        k ≫ j' = (Cocycle.coboundary F).toFun a₁ a₂ := by
    intro Z a₁ a₂
    refine baseChange_exists_comp_eq b hjq _ ?_
    change ((a₁ ≫ F) * (a₂ ≫ F)⁻¹) ≫ q' = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hFq a₁ a₂,
      mul_inv_cancel]
  let ξ := (Cocycle.coboundary F).lift _ hval
  let L := Classical.choice
    (Cocycle.nonempty_localTrivialization_of_isSplitTorus (hK.baseChange b) ξ y)
  let V : H.X.left.Opens := U'.hom ⁻¹ᵁ L.openSet
  let UW : Over C.X.left := Over.mk (V.ι ≫ U'.hom)
  let r : UW ⟶ U' := Over.homMk V.ι
  let J : UW ⟶ ((GroupScheme.baseChange b).obj H).X := L.cochain ≫ j'
  have hJ : ∀ {Z : Over C.X.left} (a₁ a₂ : Z ⟶ UW),
      (a₁ ≫ J) * (a₂ ≫ J)⁻¹ = (a₁ ≫ r ≫ F) * (a₂ ≫ r ≫ F)⁻¹ := by
    intro Z a₁ a₂
    have h := Cocycle.lift_toFun (Cocycle.coboundary F) _ hval (a₁ ≫ r) (a₂ ≫ r)
    rw [show (Cocycle.coboundary F).lift _ hval = ξ from rfl,
      L.coboundary a₁ a₂, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [J, Cocycle.coboundary, Category.assoc] using h
  let P : UW ⟶ ((GroupScheme.baseChange b).obj H).X := J⁻¹ * (r ≫ F)
  have hP : ∀ {Z : Over C.X.left} (a₁ a₂ : Z ⟶ UW), a₁ ≫ P = a₂ ≫ P := by
    intro Z a₁ a₂
    change a₁ ≫ (J⁻¹ * (r ≫ F)) = a₂ ≫ (J⁻¹ * (r ≫ F))
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
    calc (a₁ ≫ J)⁻¹ * (a₁ ≫ r ≫ F)
        = (a₁ ≫ J)⁻¹ * ((a₁ ≫ r ≫ F) * (a₂ ≫ r ≫ F)⁻¹) *
            (a₂ ≫ r ≫ F) := by group
      _ = (a₁ ≫ J)⁻¹ * ((a₁ ≫ J) * (a₂ ≫ J)⁻¹) *
            (a₂ ≫ r ≫ F) := by rw [hJ]
      _ = (a₂ ≫ J)⁻¹ * (a₂ ≫ r ≫ F) := by group
  let p : ((GroupScheme.baseChange b).obj H).X.left ⟶ H.X.left :=
    Limits.pullback.fst H.X.hom b
  have hPq : (P.left ≫ p) ≫ q.hom.hom.left = V.ι ≫ q.hom.hom.left := by
    have hPQ : baseChangePointsEquiv b H UW P ≫ q.hom.hom =
        ((Over.map b).map r ≫ e) ≫ q.hom.hom := by
      change baseChangePointsEquiv b H UW (J⁻¹ * (r ≫ F)) ≫ q.hom.hom = _
      rw [map_mul, map_inv, MonObj.mul_comp, GrpObj.inv_comp,
        baseChangePointsEquiv_naturality b H r F, MulEquiv.apply_symm_apply]
      have hJq : baseChangePointsEquiv b H UW J ≫ q.hom.hom = 1 := by
        rw [← baseChangePointsEquiv_comp, Category.assoc,
          baseChange_comp_comp_eq_one b hjq L.cochain, map_one]
      rw [hJq, inv_one, one_mul]
    have h := congrArg (fun g => g.left) hPQ
    change (P.left ≫ p) ≫ q.hom.hom.left = (V.ι ≫ 𝟙 _) ≫ q.hom.hom.left at h
    simpa only [Category.comp_id] using h
  let qW := q.hom.hom.left ∣_ L.openSet
  have hdesc : ∀ {T : Scheme.{u}} (a₁ a₂ : T ⟶ V.toScheme),
      a₁ ≫ qW = a₂ ≫ qW → a₁ ≫ (P.left ≫ p) = a₂ ≫ (P.left ≫ p) := by
    intro T a₁ a₂ hab
    have hab' : a₁ ≫ V.ι ≫ q.hom.hom.left = a₂ ≫ V.ι ≫ q.hom.hom.left := by
      have h := congrArg (fun f => f ≫ L.openSet.ι) hab
      simpa only [qW, V, U', Over.mk_hom, Category.assoc, morphismRestrict_ι] using h
    let Z : Over C.X.left := Over.mk (a₁ ≫ V.ι ≫ q.hom.hom.left)
    let a' : Z ⟶ UW := Over.homMk a₁
    let b' : Z ⟶ UW := Over.homMk a₂ hab'.symm
    exact congrArg (fun f => f.left ≫ p) (hP a' b')
  let s := EffectiveEpi.desc qW (P.left ≫ p) hdesc
  have hfac : qW ≫ s = P.left ≫ p := EffectiveEpi.fac qW _ hdesc
  refine ⟨L.openSet, L.mem_openSet, s, ?_⟩
  rw [← cancel_epi qW, ← Category.assoc, hfac, hPq]
  exact (morphismRestrict_ι q.hom.hom.left L.openSet).symm

/-- Choose the constructed scheme section near a given point of the quotient. -/
def localSection [IsAffineHom q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hK : IsSplitTorus K) (y : C.X.left) : LocalSection q y := by
  let h := exists_localSection j q hjq hK y
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.choose,
    h.choose_spec.2.choose_spec⟩

open Langlands.AlgebraicGeometry.PointTopology

/-- Over a field, a rational point's whole image lies in its chosen section
neighbourhood, giving the precise open-section input for point-topology descent. -/
theorem hasOpenSectionsAtPoints {k : Type u} [Field k]
    {A Z Q : GroupScheme (Spec (CommRingCat.of k))}
    (j : A ⟶ Z) (q : Z ⟶ Q) [Mono j.hom.hom]
    (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    [IsAffineHom q.hom.hom.left] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left] [LocallyOfFinitePresentation q.hom.hom.left]
    (hA : IsSplitTorus A) : HasOpenSectionsAtPoints k k q.hom.hom := by
  intro x
  let L := localSection j q hjq hA (x.left (⊥ : PrimeSpectrum k))
  have hbase : L.sectionMap ≫ Z.X.hom = L.openSet.ι ≫ Q.X.hom := by
    rw [← Over.w q.hom.hom, ← Category.assoc, L.section_fac]
  refine ⟨L.openSet, ?_, Over.homMk L.sectionMap hbase, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change x.left t ∈ L.openSet
    have ht : t = (⊥ : PrimeSpectrum k) :=
      @Subsingleton.elim (PrimeSpectrum k) _ t _
    rw [ht]
    exact L.mem_openSet
  · apply Over.OverMorphism.ext
    exact L.section_fac

end SplitTorusQuotient

end Langlands.GroupScheme
