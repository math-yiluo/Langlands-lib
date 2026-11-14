import Langlands.GroupScheme.SplitSolvableLocalCocycle
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Local representatives for a group-valued right coset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- A group point on a cover is locally a base point times a point of the subgroup,
with the factorization expressed on the actual restricted cover. -/
def HasLocalCosetRepresentatives (i : H ⟶ G) (g : U ⟶ G.X) : Prop :=
  ∀ y : S, ∃ W : S.Opens, y ∈ W ∧
    ∃ (s : Over.mk W.ι ⟶ G.X)
      (f : Over.mk ((U.hom ⁻¹ᵁ W).ι ≫ U.hom) ⟶ H.X),
      (Over.homMk (U.hom ⁻¹ᵁ W).ι ≫ g) * (f ≫ i.hom.hom) =
        (Over.homMk (U.hom ∣_ W) (morphismRestrict_ι U.hom W) ≫ s)

namespace LocalCosetDescent

/-- Local triviality of the subgroup-valued differences descends a right coset
to actual sections over open neighbourhoods of the base. -/
theorem hasLocalCosetRepresentatives
    (i : H ⟶ G) [Mono i.hom.hom] (g : U ⟶ G.X)
    [QuasiCompact U.hom] [Flat U.hom] [Surjective U.hom]
    (hg : ∀ {Z : Over S} (a b : Z ⟶ U),
      ∃ h : Z ⟶ H.X, h ≫ i.hom.hom = (Cocycle.coboundary g⁻¹).toFun a b)
    (hξ : ((Cocycle.coboundary g⁻¹).lift i hg).IsZariskiLocallyTrivial) :
    HasLocalCosetRepresentatives i g := by
  intro y
  let ξ := (Cocycle.coboundary g⁻¹).lift i hg
  let L := Classical.choice (hξ y)
  let W := L.openSet
  let V := U.hom ⁻¹ᵁ W
  let UW : Over S := Over.mk (V.ι ≫ U.hom)
  let r : UW ⟶ U := Over.homMk V.ι
  let f : UW ⟶ H.X := L.cochain
  let J : UW ⟶ G.X := f ≫ i.hom.hom
  have hJ : ∀ {Z : Over S} (a b : Z ⟶ UW),
      (a ≫ J) * (b ≫ J)⁻¹ = (a ≫ r ≫ g)⁻¹ * (b ≫ r ≫ g) := by
    intro Z a b
    have h := (Cocycle.coboundary g⁻¹).lift_toFun i hg (a ≫ r) (b ≫ r)
    rw [show (Cocycle.coboundary g⁻¹).lift i hg = ξ from rfl,
      L.coboundary a b, MonObj.mul_comp, GrpObj.inv_comp] at h
    simpa only [Cocycle.coboundary, GrpObj.comp_inv, inv_inv, J, f, Category.assoc] using h
  let P : UW ⟶ G.X := (r ≫ g) * J
  have hP : ∀ {Z : Over S} (a b : Z ⟶ UW), a ≫ P = b ≫ P := by
    intro Z a b
    simp only [P, MonObj.comp_mul]
    calc
      (a ≫ r ≫ g) * (a ≫ J) =
          (a ≫ r ≫ g) * ((a ≫ J) * (b ≫ J)⁻¹) * (b ≫ J) := by group
      _ = (a ≫ r ≫ g) * ((a ≫ r ≫ g)⁻¹ * (b ≫ r ≫ g)) *
          (b ≫ J) := by rw [hJ]
      _ = (b ≫ r ≫ g) * (b ≫ J) := by group
  let qW := U.hom ∣_ W
  have hdesc : ∀ {Z : Scheme.{u}} (a b : Z ⟶ V.toScheme),
      a ≫ qW = b ≫ qW → a ≫ P.left = b ≫ P.left := by
    intro Z a b hab
    have hab' : b ≫ V.ι ≫ U.hom = a ≫ V.ι ≫ U.hom := by
      have h := congrArg (fun v => v ≫ W.ι) hab.symm
      simpa only [qW, V, Category.assoc, morphismRestrict_ι] using h
    exact congrArg (fun v => v.left)
      (hP (Z := Over.mk (a ≫ V.ι ≫ U.hom))
        (Over.homMk a) (Over.homMk b hab'))
  let s₀ := EffectiveEpi.desc qW P.left hdesc
  have hs₀ : qW ≫ s₀ = P.left := EffectiveEpi.fac qW P.left hdesc
  have hs : s₀ ≫ G.X.hom = W.ι := by
    rw [← cancel_epi qW, ← Category.assoc, hs₀, Over.w P]
    exact (morphismRestrict_ι U.hom W).symm
  let s : Over.mk W.ι ⟶ G.X := Over.homMk s₀ hs
  refine ⟨W, L.mem_openSet, s, f, ?_⟩
  apply Over.OverMorphism.ext
  exact hs₀.symm

variable {R : CommRingCat.{u}} {K B T G : GroupScheme (Spec R)}

/-- An affine subgroup with a split-torus quotient and a finite vector-series
kernel has local right coset representatives on affine faithfully flat covers. -/
theorem hasLocalCosetRepresentatives_of_vectorSeries
    (i : B ⟶ G) [Mono i.hom.hom]
    (j : K ⟶ B) (q : B ⟶ T) [Mono j.hom.hom]
    (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    [IsAffine B.X.left] [IsAffine T.X.left] [IsAffineHom K.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {n : ℕ} (hK : HasAffineVectorSeries n K) (hT : IsSplitTorus T)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (g : U ⟶ G.X)
    (hg : ∀ {Z : Over (Spec R)} (a b : Z ⟶ U),
      ∃ h : Z ⟶ B.X, h ≫ i.hom.hom = (Cocycle.coboundary g⁻¹).toFun a b) :
    HasLocalCosetRepresentatives i g :=
  hasLocalCosetRepresentatives i g hg
    (SplitSolvableLocalCocycle.isZariskiLocallyTrivial_of_vectorSeries j q hjq hK hT U
      ((Cocycle.coboundary g⁻¹).lift i hg))

end LocalCosetDescent

end Langlands.GroupScheme
