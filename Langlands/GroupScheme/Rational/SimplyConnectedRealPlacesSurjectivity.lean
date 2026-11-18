import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesCohomologyStatement
import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.Torus.Maximal
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints

/-! # Reduction of real-place surjectivity to tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The real infinite places of a number field. -/
abbrev RealPlaceIndex (F : Type u) [Field F] := {w : InfinitePlace F // w.IsReal}

variable {F : Type u} [Field F] [NumberField F]

/-- The base map from the actual completion at a real place. -/
abbrev realPlaceBaseMap (w : RealPlaceIndex F) :
    Spec (CommRingCat.of (Langlands.Global.placeCompletion F (.inl w.1))) ⟶
      Spec (CommRingCat.of F) :=
  algebraBaseMap F (Langlands.Global.placeCompletion F (.inl w.1))

/-- A family of cocycles on the pullbacks of the same cover to the real places. -/
abbrev RealPlaceCocycles (G : GroupScheme (Spec (CommRingCat.of F)))
    (U : Over (Spec (CommRingCat.of F))) :=
  ∀ w : RealPlaceIndex F, Cocycle ((baseChange (realPlaceBaseMap w)).obj G)
    ((Over.pullback (realPlaceBaseMap w)).obj U)

namespace Cocycle

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  {U : Over (Spec (CommRingCat.of F))}

/-- Base change a cocycle to the completion at a real place and pull back its cover. -/
abbrev localizeReal (ξ : Cocycle G U) (w : RealPlaceIndex F) :=
  ξ.baseChange (realPlaceBaseMap w) _
    ((Over.mapPullbackAdj (realPlaceBaseMap w)).counit.app U)

/-- Real-place localization is surjective on cohomology, allowing finite separable
refinement of the cover. -/
def RealPlacesSurjectivity (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (c : RealPlaceCocycles G (ringTest F L)),
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E)
      (_ : Algebra.IsSeparable F E) (e : L →ₐ[F] E) (ξ : Cocycle G (ringTest F E)),
      ∀ w : RealPlaceIndex F,
        (ξ.localizeReal w).Cohomologous
          ((c w).refine ((Over.pullback (realPlaceBaseMap w)).map (ringTestMap F e)))

end Cocycle

/-- Real-place cocycles come from maximal tori after one finite separable refinement
of the global field cover. -/
def RealPlacesToralRepresentativesStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
      (c : RealPlaceCocycles G (ringTest F L)),
      ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E)
        (_ : Algebra.IsSeparable F E) (e : L →ₐ[F] E),
        ∀ w : RealPlaceIndex F,
          let b := realPlaceBaseMap w
          ∃ (T : CommGroupScheme (Spec (CommRingCat.of
                (Langlands.Global.placeCompletion F (.inl w.1)))))
            (j : T.toGrp ⟶ (baseChange b).obj G)
            (_ : IsMaximalTorus (k := w.1.Completion) (T := T) j)
            (d : Cocycle T.toGrp ((Over.pullback b).obj (ringTest F E))),
            (d.map j).Cohomologous
              ((c w).refine ((Over.pullback b).map (ringTestMap F e)))

/-- A family of real maximal tori in a connected reductive group admits a global maximal
torus conjugate to each of them by a point over the corresponding completion. -/
def SimultaneousRealMaximalTorusApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G →
    ∀ (T : ∀ w : RealPlaceIndex F, CommGroupScheme (Spec (CommRingCat.of
          (Langlands.Global.placeCompletion F (.inl w.1)))))
      (j : ∀ w, (T w).toGrp ⟶ (baseChange (realPlaceBaseMap w)).obj G),
      (∀ w, IsMaximalTorus (k := w.1.Completion) (T := T w) (j w)) →
      ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (i : T₀.toGrp ⟶ G),
        IsMaximalTorus (T := T₀) i ∧
        ∀ w : RealPlaceIndex F,
          let b := realPlaceBaseMap w
          ∃ (a : (baseChange b).obj T₀.toGrp ≅ (T w).toGrp)
            (g : Over.mk (𝟙 _) ⟶ ((baseChange b).obj G).X),
            (baseChange b).map i ≫ (((baseChange b).obj G).innerIso g).hom = a.hom ≫ j w

/-- Real-place localization in first cohomology is surjective for tori. -/
def RealPlacesTorusCohomologySurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (T : CommGroupScheme (Spec (CommRingCat.of F))),
    IsTorus T.toGrp → Cocycle.RealPlacesSurjectivity T.toGrp

/-- The surjectivity clause of `SimplyConnectedRealPlacesCohomologyStatement`,
using the Library's fixed-cover cohomology relation. -/
def SimplyConnectedRealPlacesSurjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F))),
    IsSimplyConnected G → Cocycle.RealPlacesSurjectivity G

namespace Cocycle

variable {S S' : Scheme.{u}} {G H J : GroupScheme S} {U V W : Over S}

private theorem eq_of_toFun_eq {ξ ζ : Cocycle G U}
    (h : ∀ {Z : Over S} (x y : Z ⟶ U), ξ.toFun x y = ζ.toFun x y) : ξ = ζ := by
  cases ξ
  cases ζ
  congr
  funext Z x y
  exact h x y

private theorem map_comp (ξ : Cocycle G U) (i : G ⟶ H) (j : H ⟶ J) :
    (ξ.map i).map j = ξ.map (i ≫ j) := by
  apply eq_of_toFun_eq
  intro Z x y
  change (ξ.toFun x y ≫ i.hom.hom) ≫ j.hom.hom = ξ.toFun x y ≫ (i ≫ j).hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]

private theorem map_refine (ξ : Cocycle G U) (i : G ⟶ H) (s : V ⟶ U) :
    (ξ.map i).refine s = (ξ.refine s).map i := rfl

private theorem refine_comp (ξ : Cocycle G U) (s : V ⟶ U) (t : W ⟶ V) :
    (ξ.refine s).refine t = ξ.refine (t ≫ s) := by
  apply eq_of_toFun_eq
  intro Z x y
  simp only [refine_toFun, Category.assoc]

private theorem baseChange_map (ξ : Cocycle G U) (i : G ⟶ H) (b : S' ⟶ S)
    (P : Over S') (r : (Over.map b).obj P ⟶ U) :
    (ξ.map i).baseChange b P r = (ξ.baseChange b P r).map ((GroupScheme.baseChange b).map i) := by
  apply eq_of_toFun_eq
  intro Z x y
  apply (baseChangePointsEquiv b H Z).injective
  change baseChangePointsEquiv b H Z (((ξ.map i).baseChange b P r).toFun x y) =
    baseChangePointsEquiv b H Z
      ((ξ.baseChange b P r).toFun x y ≫ ((GroupScheme.baseChange b).map i).hom.hom)
  rw [baseChange_toFun, baseChangePointsEquiv_comp, baseChange_toFun]
  rfl

private theorem cohomologous_map_inner (ξ : Cocycle G U)
    (g : Over.mk (𝟙 S) ⟶ G.X) : ξ.Cohomologous (ξ.map (G.innerIso g).hom) := by
  refine ⟨(G.constantPoint g U)⁻¹, fun {Z} x y => ?_⟩
  simp only [map, comp_innerIso_hom, twist, GrpObj.comp_inv, constantPoint_naturality, inv_inv]

end Cocycle

open Cocycle in
/-- Push a localized torus class into the ambient group. Conjugation by a rational point
changes the pushforward by a constant cochain, and the two field refinements compose. -/
theorem simplyConnectedRealPlacesSurjectivity_of_tori
    (hrep : RealPlacesToralRepresentativesStatement.{u})
    (happrox : SimultaneousRealMaximalTorusApproximationStatement.{u})
    (htorus : RealPlacesTorusCohomologySurjectivityStatement.{u}) :
    SimplyConnectedRealPlacesSurjectivityStatement.{u} := by
  classical
  intro F _ _ G hG L _ _ _ _ c
  obtain ⟨E, _, _, _, _, e, hE⟩ := hrep F G hG L c
  choose T j hmax d hd using hE
  obtain ⟨T₀, i, hi, hconj⟩ := happrox F G hG.isSemisimple.isConnectedReductive T j hmax
  choose a g hag using hconj
  let d₀ : RealPlaceCocycles T₀.toGrp (ringTest F E) := fun w => (d w).map (a w).inv
  obtain ⟨M, _, _, _, _, f, θ, hθ⟩ := htorus F T₀ hi.1 E d₀
  refine ⟨M, ‹Field M›, ‹Algebra F M›, ‹FiniteDimensional F M›, ‹Algebra.IsSeparable F M›,
    f.comp e, θ.map i, fun w => ?_⟩
  let b := realPlaceBaseMap w
  let r := (Over.mapPullbackAdj b).counit.app (ringTest F M)
  let t := (Over.pullback b).map (ringTestMap F f)
  let s := (Over.pullback b).map (ringTestMap F e)
  let i₀ := (baseChange b).map i
  have h₁ : ((θ.map i).localizeReal w).Cohomologous (((d₀ w).map i₀).refine t) := by
    rw [show (θ.map i).localizeReal w = (θ.localizeReal w).map i₀ from
      baseChange_map θ i b _ r, map_refine]
    exact (hθ w).map i₀
  have hpush : ((d₀ w).map i₀).map (((baseChange b).obj G).innerIso (g w)).hom =
      (d w).map (j w) := by
    rw [map_comp, show i₀ ≫ (((baseChange b).obj G).innerIso (g w)).hom =
      (a w).hom ≫ j w from hag w]
    change ((d w).map (a w).inv).map ((a w).hom ≫ j w) = (d w).map (j w)
    rw [map_comp, Iso.inv_hom_id_assoc]
  have h₂ := (cohomologous_map_inner ((d₀ w).map i₀) (g w)).refine t
  rw [hpush] at h₂
  have h₃ : (((d w).map (j w)).refine t).Cohomologous (((c w).refine s).refine t) :=
    (hd w).refine t
  rw [refine_comp] at h₃
  change ((θ.map i).localizeReal w).Cohomologous
    ((c w).refine ((Over.pullback b).map (ringTestMap F (f.comp e))))
  rw [ringTestMap_comp, Functor.map_comp]
  exact h₁.trans (h₂.trans h₃)

end Langlands.GroupScheme
