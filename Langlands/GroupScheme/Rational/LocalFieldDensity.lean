import Langlands.AlgebraicGeometry.PointTopology.AffineDensity
import Langlands.GroupScheme.Rational.RationalCenterComparisonProof

/-! # Rational-point density for smooth connected affine groups over local fields -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Algebra points separating nonzero elements give dense actual rational points. -/
theorem hasDenseRationalPoints_spectrum_of_separating
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (hsep : ∀ a : A, a ≠ 0 → ∃ y : A →ₐ[k] k, y a ≠ 0) :
    HasDenseRationalPoints k
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) := by
  have hd : Dense (Set.range fun y : A →ₐ[k] k =>
      PrimeSpectrum.comap y.toRingHom (⟨⊥, inferInstance⟩ : PrimeSpectrum k)) := by
    apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
    rintro _ ⟨a, rfl⟩ ⟨p, hp⟩
    have ha : a ≠ 0 := by
      intro h
      simp [h] at hp
    obtain ⟨y, hy⟩ := hsep a ha
    refine ⟨_, ?_, y, rfl⟩
    simpa using hy
  apply hd.mono
  rintro _ ⟨y, rfl⟩
  let q : RationalPoint k
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom y.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom y.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _
      rw [← Spec.map_comp]
      convert Spec.map_id (CommRingCat.of k) using 1
      congr 1
      ext r
      exact y.commutes r)
  exact Set.mem_iUnion.mpr ⟨q, ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum k), rfl⟩⟩

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- Smooth connected affine groups over actual nonarchimedean local fields have
Zariski dense rational points. -/
def SmoothConnectedAffineLocalFieldDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      HasDenseRationalPoints F G.X

/-- The density uses the local-field smooth-domain separation theorem and the
identity point, with no reductivity or characteristic assumption. -/
theorem hasDenseRationalPoints_of_localField
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left] :
    HasDenseRationalPoints F G.X := by
  have := CharacterLatticeProof.isDomain_coord G
  set D := Lie.coordinateAlgebra G
  have hsm : Smooth ((algSpec (CommRingCat.of F)).obj (op D)).hom := by
    have : IsIso (Lie.coordinateIso G).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (Lie.coordinateIso G).hom))
    have h : Smooth ((Lie.coordinateIso G).hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of F) D))) at hsm
  have : Algebra.Smooth (CommRingCat.of F) D :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hsm)
  have hd := hasDenseRationalPoints_spectrum_of_separating F D fun d hd =>
    RationalCenterComparisonProof.exists_algHom_apply_ne_zero_of_localField F
      (Lie.coordinateOrigin G) hd
  apply hasDenseRationalPoints_of_denseRange (Lie.coordinateIso G).hom ?_ hd
  apply Function.Surjective.denseRange
  intro x
  refine ⟨(Lie.coordinateIso G).inv.left x, ?_⟩
  change ((Lie.coordinateIso G).inv.left ≫ (Lie.coordinateIso G).hom.left) x = x
  have h := congrArg (fun f => f.left) (Lie.coordinateIso G).inv_hom_id
  exact congrArg (fun f : G.X.left ⟶ G.X.left => f x) h

/-- The complete arbitrary-universe local-field density statement. -/
theorem smoothConnectedAffineLocalFieldDensity :
    SmoothConnectedAffineLocalFieldDensityStatement.{u} := by
  intro F _ _ _ _ G hsm haff hconn
  let := hsm
  let := haff
  let := hconn
  exact hasDenseRationalPoints_of_localField F G

end Langlands.GroupScheme
