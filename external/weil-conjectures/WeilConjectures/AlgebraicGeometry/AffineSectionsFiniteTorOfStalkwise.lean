/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise
import WeilConjectures.Algebra.Homology.FlatResolutionTorComparison
import Mathlib.RingTheory.Flat.Stability

/-! # Affine coordinate Tor bounds from stalkwise bounds

Source: Stacks Project, Tag 069C.
(blueprint: lem-pc-affine-sections-finite-tor-of-stalkwise).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite stalk Tor dimensions give a finite Tor bound for an affine coordinate ring.
Source: Stacks Project, Tag 069C, `lemma-check-perfect-stalks`, (3) implies (1),
and the first sentence of the proof of (1) implies (2).

Proof: put A = Γ(Y,U), B = Γ(X,V). The map A to B induced by f is of finite
type because U and V are affine. A is Noetherian, so a finite polynomial
presentation P = A[t₁,...,tₙ] surjecting onto B makes B a pseudo-coherent
P-module, concentrated in degree zero. For a prime q of P outside the support
of B, B_q is zero. Otherwise q corresponds to a source point y in V and
B_q identifies with the source local ring. The hypothesis gives finite Tor
dimension over the localization of A at the image prime. The localized
polynomial algebra is flat over that localization and its fibres have finite
global dimension, bounded by n. Tag 068X therefore makes B_q perfect over P_q.
Tag 068W, applied to the bounded-below pseudo-coherent complex B[0], makes B
perfect over P. A bounded resolution by finite projective P-modules is a bounded
flat A-resolution, since P is flat over A. Choose d so that this resolution is
zero below degree -d. Tensoring with any A-module gives Tor vanishing above d;
compute Tor' with a projective resolution and compare it to this flat resolution.
The empty affine source has B = 0 and permits d = 0; no bound on dim A is used.
(blueprint: lem-pc-affine-sections-finite-tor-of-stalkwise). -/
theorem affineSections_finiteTorDimension_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) :
    ∃ d : ℕ, ∀ M : ModuleCat.{u} Γ(Y, U), ∀ j : ℕ, d < j →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) j).obj
        ((ModuleCat.restrictScalars (f.appLE U V e).hom).obj
          (ModuleCat.of Γ(X, V) Γ(X, V)))).obj M) := by
  classical
  let A := Γ(Y, U)
  let B := Γ(X, V)
  let φ : A →+* B := (f.appLE U V e).hom
  let : Algebra A B := φ.toAlgebra
  have hfinite : Algebra.FiniteType A B := f.finiteType_appLE hU hV e
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hfinite
  have hcomp : g.toRingHom.comp MvPolynomial.C = φ := by
    ext a
    exact g.commutes a
  obtain ⟨d, P, hP⟩ := affinePolynomial_boundedResolution_of_stalkwise
    f hperfect U hU V hV e n g.toRingHom hg hcomp
  let res := ModuleCat.restrictScalars (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
  let F := (res.mapHomologicalComplex (.down ℕ)).obj P.complex
  let M₀ := res.obj ((ModuleCat.restrictScalars g.toRingHom).obj (ModuleCat.of B B))
  have hflat (i : ℕ) : Module.Flat A (F.X i) := by
    have : Module.Projective (MvPolynomial (Fin n) A) (P.complex.X i) :=
      inferInstance
    have : Module.Flat (MvPolynomial (Fin n) A) (P.complex.X i) :=
      Module.Flat.of_projective
    let : Module A (P.complex.X i) :=
      Module.compHom _ (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
    have : IsScalarTower A (MvPolynomial (Fin n) A) (P.complex.X i) :=
      IsScalarTower.of_compHom A (MvPolynomial (Fin n) A) (P.complex.X i)
    exact Module.Flat.trans A (MvPolynomial (Fin n) A) (P.complex.X i)
  let ε : F ⟶ (ChainComplex.single₀ (ModuleCat.{u} A)).obj M₀ := by
    exact (res.mapHomologicalComplex (.down ℕ)).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex res (.down ℕ) 0).hom.app _
  have : QuasiIso ε := by
    dsimp [ε]
    infer_instance
  let eM := ModuleCat.restrictScalarsComp'App MvPolynomial.C g.toRingHom φ
    hcomp.symm (ModuleCat.of B B)
  refine ⟨d, fun N j hj ↦ ?_⟩
  obtain ⟨eTor⟩ := ModuleCat.flatResolution_torComparison M₀ F ε hflat N j
  have hz : IsZero
      ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (.down ℕ)).obj F).X j) :=
    (CategoryTheory.MonoidalCategory.tensorRight N).map_isZero (res.map_isZero (hP j hj))
  have hhom := (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
  have htor := hhom.of_iso eTor
  exact htor.of_iso (((Tor' (ModuleCat.{u} A) j).mapIso eM).app N)

end AlgebraicGeometry
