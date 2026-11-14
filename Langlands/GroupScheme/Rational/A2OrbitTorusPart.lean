import Langlands.Geometry.Building.KPTorusCharacterFiltration
import Langlands.GroupScheme.Rational.A2OrbitDescent
import Langlands.GroupScheme.Rational.PieceTorusCharacter
import Langlands.Geometry.Building.SplitTorusNormalizerBaseChange
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.Geometry.Building.QuasiSplitApartmentAssembly

/-! # Torus parts of rational opposite products over a splitting field

For Galois-compatible pinning data `D` and a maximal split torus `S ⟶ D.torus ⟶ G`, let
`X, X₀` be rational points of the relative root group of `a` whose scalar extensions are
products of piece triples, `X₀` with merged-root coordinates `1`. The ratio of their
rational opposite products extends to a point of the pinned torus whose characters
orthogonal to the `q`-coroots are the products of the merged-root coordinates. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GaloisPointComparison Langlands.Geometry.Building

namespace Langlands.GroupScheme

/-- A normalizer point of `j` normalizes the composite of `j` with an isomorphism of tori. -/
theorem mem_normalizerPoints_groupHom_comp {B : Scheme.{u}} {T T' : CommGroupScheme B}
    {G : GroupScheme B} (e : T' ≅ T) (j : T.toGrp ⟶ G) {n : Over.mk (𝟙 B) ⟶ G.X}
    (hn : n ∈ normalizerPoints j) :
    n ∈ normalizerPoints (CommGroupScheme.groupHom e.hom ≫ j) := by
  obtain ⟨σ, hσ⟩ := hn
  refine ⟨e ≪≫ σ ≪≫ e.symm, ?_⟩
  unfold IsNormalizingPoint at hσ ⊢
  rw [Category.assoc, hσ, ← Category.assoc, ← Category.assoc]
  congr 1
  change CommGroupScheme.groupHom (e.hom ≫ σ.hom) =
    CommGroupScheme.groupHom ((e.hom ≫ σ.hom ≫ e.inv) ≫ e.hom)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)

local instance a2OrbitTorusPartAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

omit [IsAffineHom G.X.hom] in
theorem rationalExtend_injective' [IsAffineHom G.X.hom] :
    Function.Injective (rationalExtend k K G) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact Langlands.Geometry.Building.rationalExtend_injective_of_isAffine k K G

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)
  {a : characterLattice S}

/-- **Torus part of a ratio of rational opposite products.** -/
theorem exists_rationalTorusPart [LocallyOfFiniteType G.X.hom]
    (hic : IsClosedSubgroup (CommGroupScheme.groupHom t ≫ D.inclusion))
    (hjc : IsClosedSubgroup D.inclusion)
    (hS : IsSplitTorus S.toGrp) (ha0 : a ≠ 0)
    (hline : RestrictsToMultipliableLine (D.restrictMap t) D.pinning.rootDatum
      (characterLattice.baseChange (algebraBaseMap k K) S a))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
    (F : PieceFamily (D.restrictMap t) D.pinning.rootDatum
      (characterLattice.baseChange (algebraBaseMap k K) S a))
    (xm : ∀ l, D.pinning.RootParametrization (F.lm l)) (w : Fin F.r → Kˣ)
    {Xq Yp : Fin F.r → rationalPoints (baseChanged k K G)}
    (hXq : ∀ l, Xq l ∈ rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lq l)))
    (hYp : ∀ l, Yp l ∈ rootGroupPoints D.pinning.inclusion (D.pinning.rootDatum.root (F.lp l)))
    {X X₀ A B A₀ B₀ : rationalPoints G}
    (hXK : rationalExtend k K G X = F.tripleProd Xq (fun l => (xm l).rationalPoint (w l)) Yp)
    (hX₀K : rationalExtend k K G X₀ =
      F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1))
    (hX : X ∈ rootGroupPoints (CommGroupScheme.groupHom t ≫ D.inclusion) a) (hX1 : X ≠ 1)
    (hX₀ : X₀ ∈ rootGroupPoints (CommGroupScheme.groupHom t ≫ D.inclusion) a) (hX₀1 : X₀ ≠ 1)
    (hAB : RelativeRoot.IsOppositeFactorPair (CommGroupScheme.groupHom t ≫ D.inclusion) a X
      (A, B))
    (hAB₀ : RelativeRoot.IsOppositeFactorPair (CommGroupScheme.groupHom t ≫ D.inclusion) a X₀
      (A₀, B₀)) :
    ∃ x : rationalPoints D.pinning.torus.toGrp,
      rationalExtend k K G (A * X * B * (A₀ * X₀ * B₀)⁻¹) =
        rationalPoints.map D.pinning.inclusion x ∧
      ∀ ω : characterLattice D.pinning.torus,
        (∀ l, D.pinning.rootDatum.toLinearMap ω (D.pinning.rootDatum.coroot (F.lq l)) = 0) →
          D.pinning.charEval ω x =
            ∏ l, (w l) ^
              D.pinning.rootDatum.toLinearMap ω (D.pinning.rootDatum.coroot (F.lp l)) := by
  have : Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    D.pinning.isConnectedReductive.smooth
  have : LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have hfac := D.groupHom_restrictMap_comp_inclusion t
  have : Mono (CommGroupScheme.groupHom t ≫ D.inclusion).hom.hom.left := hic.mono
  have : Mono D.inclusion.hom.hom.left := hjc.mono
  have : Mono (CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion).hom.hom.left := by
    rw [hfac]; exact (hic.baseChange (algebraBaseMap k K)).mono
  have hSK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S).toGrp :=
    hS.baseChange (algebraBaseMap k K)
  have ha0K : characterLattice.baseChange (algebraBaseMap k K) S a ≠ 0 := by
    intro h
    apply ha0
    apply (characterLattice.baseChangeEquiv (algebraBaseMap k K) S hS).map_eq_zero_iff.mp
    rw [characterLattice.baseChangeEquiv_apply, h]
  -- memberships after scalar extension
  have hmemA : ∀ {g : rationalPoints G} {c : characterLattice S},
      g ∈ rootGroupPoints (CommGroupScheme.groupHom t ≫ D.inclusion) c →
      rationalExtend k K G g ∈ rootGroupPoints
        (CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion)
        (characterLattice.baseChange (algebraBaseMap k K) S c) := by
    intro g c hg
    rw [hfac]
    exact rationalExtend_mem_rootGroupPoints (K := K) _ c hg
  have hmemN : ∀ {n : rationalPoints G},
      n ∈ normalizerPoints (CommGroupScheme.groupHom t ≫ D.inclusion) →
      rationalExtend k K G n ∈ normalizerPoints D.pinning.inclusion ∧
        rationalExtend k K G n ∈ normalizerPoints
          (CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion) := by
    intro n hn
    refine ⟨?_, ?_⟩
    · rw [D.inclusion_eq]
      apply mem_normalizerPoints_groupHom_comp
      have h1 := mem_normalizerPoints_of_torusCentralizer _ D.inclusion hcent ⟨n, hn⟩
      exact (normalizerPointsFieldExtend (K := K) D.inclusion ⟨n, h1⟩).prop
    · rw [hfac]
      exact (normalizerPointsFieldExtend (K := K) _ ⟨n, hn⟩).prop
  have hneg : ∀ {g : rationalPoints G},
      g ∈ rootGroupPoints (CommGroupScheme.groupHom t ≫ D.inclusion) (-a) →
      rationalExtend k K G g ∈ rootGroupPoints
        (CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion)
        (-characterLattice.baseChange (algebraBaseMap k K) S a) := by
    intro g hg
    rw [← map_neg]
    exact hmemA hg
  have hg := hmemA hX
  rw [hXK] at hg
  have hg₀ := hmemA hX₀
  rw [hX₀K] at hg₀
  have hg1 : F.tripleProd Xq (fun l => (xm l).rationalPoint (w l)) Yp ≠ 1 := by
    rw [← hXK]
    intro h
    exact hX1 (rationalExtend_injective' (by rw [h, map_one]))
  have hg₀1 : F.tripleProd (fun _ => 1) (fun l => (xm l).rationalPoint 1) (fun _ => 1) ≠ 1 := by
    rw [← hX₀K]
    intro h
    exact hX₀1 (rationalExtend_injective' (by rw [h, map_one]))
  obtain ⟨hN, hN'⟩ := hmemN hAB.2.2
  obtain ⟨hN₀, hN₀'⟩ := hmemN hAB₀.2.2
  rw [map_mul, map_mul, hXK] at hN hN'
  rw [map_mul, map_mul, hX₀K] at hN₀ hN₀'
  obtain ⟨x, hx, hxω⟩ := D.pinning.exists_oppositeProducts_torusPart hline hSK F ha0K xm w hXq
    hYp hg hg1 (hneg hAB.1) (hneg hAB.2.1) hN hN' hg₀ hg₀1 (hneg hAB₀.1) (hneg hAB₀.2.1) hN₀ hN₀'
  refine ⟨x, ?_, hxω⟩
  rw [map_mul, map_inv, map_mul, map_mul, map_mul, map_mul, hXK, hX₀K, hx]

end GaloisCompatiblePinningData

end Langlands.GroupScheme
