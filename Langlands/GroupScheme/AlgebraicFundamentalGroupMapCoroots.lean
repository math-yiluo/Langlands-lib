import Langlands.GroupScheme.AlgebraicFundamentalGroupMapConstruction

/-! # Coroot preservation for actual geometric torus factorizations -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k H) (b : Choice k G) (f : H ⟶ G)
  (E : Type u) [Field E] [Algebra k E]

@[reassoc]
theorem scInclusion_comp :
    a.scInclusion ≫ (a.covering ≫ a.derivedInclusion) =
      CommGroupScheme.groupHom a.scToTorus ≫ a.inclusion :=
  subgroupIntersection_condition _ _

variable
  (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus)
  (he : a.IsTorusFactorization E b f e)

/-- The actual restriction of the lifted cover homomorphism to the full
geometric preimage tori, constructed by the pullback universal property. -/
def geometricPreimageMap :
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.scTorus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.scTorus :=
  Additive.ofMul
    (((IsPullback.of_hasPullback (b.covering ≫ b.derivedInclusion) b.inclusion).map
      (GroupScheme.baseChange (algebraBaseMap k E))).lift
      ((GroupScheme.baseChange (algebraBaseMap k E)).map a.scInclusion ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map (a.coverMap b f))
      ((GroupScheme.baseChange (algebraBaseMap k E)).map
        (CommGroupScheme.groupHom a.scToTorus) ≫ CommGroupScheme.groupHom e)
      (by
        let F := GroupScheme.baseChange (algebraBaseMap k E)
        change (F.map a.scInclusion ≫ F.map (a.coverMap b f)) ≫
            F.map (b.covering ≫ b.derivedInclusion) =
          (F.map (CommGroupScheme.groupHom a.scToTorus) ≫
            CommGroupScheme.groupHom e) ≫ F.map b.inclusion
        calc
          _ = F.map a.scInclusion ≫
              F.map (a.coverMap b f ≫ (b.covering ≫ b.derivedInclusion)) := by
            simp only [Functor.map_comp, Category.assoc]
          _ = F.map (a.scInclusion ≫ (a.covering ≫ a.derivedInclusion)) ≫
              F.map f := by
            rw [coverMap_comp_ambient]
            simp only [Functor.map_comp, Category.assoc]
          _ = F.map (CommGroupScheme.groupHom a.scToTorus ≫ a.inclusion) ≫
              F.map f := by rw [scInclusion_comp]
          _ = _ := by
            simpa only [Functor.map_comp, Category.assoc] using
              congrArg (fun t =>
                F.map (CommGroupScheme.groupHom a.scToTorus) ≫ t) he))

@[reassoc]
theorem geometricPreimageMap_comp :
    a.geometricPreimageMap b f E e he ≫
        (CommGroupScheme.baseChange (algebraBaseMap k E)).map b.scToTorus =
      (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus ≫ e := by
  apply Additive.ofMul.injective
  exact ((IsPullback.of_hasPullback (b.covering ≫ b.derivedInclusion)
    b.inclusion).map (GroupScheme.baseChange (algebraBaseMap k E))).lift_snd _ _ _

/-- Postcomposition by the geometric torus restriction on integral lattices. -/
def torusLatticeMap : a.lattice E →ₗ[ℤ] b.lattice E :=
  (AddMonoidHom.mk' (fun ν => ν ≫ e)
    (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)).toIntLinearMap

include he in
/-- The lifted restriction maps the source coroot image into the target image. -/
theorem torusLatticeMap_corootImage :
    a.corootImage E ≤ (b.corootImage E).comap (a.torusLatticeMap b E e) := by
  rintro _ ⟨ν, rfl⟩
  refine ⟨ν ≫ a.geometricPreimageMap b f E e he, ?_⟩
  change (ν ≫ a.geometricPreimageMap b f E e he) ≫
      (CommGroupScheme.baseChange (algebraBaseMap k E)).map b.scToTorus =
    (ν ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus) ≫ e
  rw [Category.assoc, geometricPreimageMap_comp, Category.assoc]

/-- The quotient homomorphism supplied by one actual torus factorization. -/
def factorizationMap : a.atChoice E →ₗ[ℤ] b.atChoice E :=
  (a.corootImage E).mapQ (b.corootImage E) (a.torusLatticeMap b E e)
    (a.torusLatticeMap_corootImage b f E e he)

@[simp]
theorem factorizationMap_projection (ν : a.lattice E) :
    a.factorizationMap b f E e he (a.projection E ν) =
      b.projection E (ν ≫ e) := rfl

end Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice
