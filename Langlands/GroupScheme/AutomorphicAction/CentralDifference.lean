import Langlands.GroupScheme.QuotientAction
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.Characters

/-! # Difference families for actions on central extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {G H N Q : GroupScheme S}
variable (a : AutomorphicAction G H) (j : N ⟶ H) (p : H ⟶ Q)

/-- The difference between the action and the identity, before taking the quotient. -/
def differenceHom : G.X ⊗ H.X ⟶ H.X :=
  (snd G.X H.X)⁻¹ * a.hom

theorem lift_differenceHom {T : Over S} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    lift g x ≫ differenceHom a = x⁻¹ * a.act g x := by
  simp only [differenceHom, MonObj.comp_mul, GrpObj.comp_inv, lift_snd]
  rfl

variable (hker : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range j)
variable (hQ : ∀ (T : Over S) (g : T ⟶ G.X) (x : T ⟶ H.X),
  a.act g x ≫ p.hom.hom = x ≫ p.hom.hom)

include hker hQ

/-- A trivial action on the quotient makes every difference a point of the kernel. -/
theorem difference_mem_range {T : Over S} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    x⁻¹ * a.act g x ∈ (SubgroupFunctor.range j).carrier T := by
  rw [← hker, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, hQ,
    inv_mul_cancel]

variable [Mono j.hom.hom]

/-- The difference morphism factored through the specified kernel inclusion. -/
def differenceLift : G.X ⊗ H.X ⟶ N.X :=
  (SubgroupFunctor.IsRepresentedBy.pointsEquiv
    (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩) _).symm
      ⟨differenceHom a, by
        simpa only [← lift_differenceHom, lift_fst_snd, Category.id_comp] using
          difference_mem_range a j p hker hQ (fst G.X H.X) (snd G.X H.X)⟩

@[reassoc]
theorem differenceLift_comp :
    differenceLift a j p hker hQ ≫ j.hom.hom = differenceHom a :=
  SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp
    (show (SubgroupFunctor.range j).IsRepresentedBy j from ⟨inferInstance, rfl⟩) _

theorem lift_differenceLift_comp {T : Over S} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    (lift g x ≫ differenceLift a j p hker hQ) ≫ j.hom.hom = x⁻¹ * a.act g x := by
  rw [Category.assoc, differenceLift_comp, lift_differenceHom]

variable (hN : ∀ (T : Over S) (g : T ⟶ G.X) (n : T ⟶ N.X),
  a.act g (n ≫ j.hom.hom) = n ≫ j.hom.hom)

include hN

omit hQ [Mono j.hom.hom] in
/-- When the action fixes the kernel, the difference is constant on quotient fibers. -/
theorem difference_eq_of_comp_eq {T : Over S} (g : T ⟶ G.X) (x y : T ⟶ H.X)
    (he : x ≫ p.hom.hom = y ≫ p.hom.hom) :
    x⁻¹ * a.act g x = y⁻¹ * a.act g y := by
  have hd : x / y ∈ (SubgroupFunctor.range j).carrier T := by
    rw [← hker, mem_range_kernelι_iff, GrpObj.div_comp, he, div_self']
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp hd
  have ha : a.act g (x / y) = x / y := by
    rw [← hn, hN]
  have hx : x = (x / y) * y := (div_mul_cancel x y).symm
  calc
    x⁻¹ * a.act g x = ((x / y) * y)⁻¹ * a.act g ((x / y) * y) := by rw [← hx]
    _ = y⁻¹ * a.act g y := by rw [a.act_mul_right, ha]; group

/-- The kernel-valued difference coequalizes the fibers of `G × p`. -/
theorem differenceLift_eq_of_comp_eq {T : Over S}
    (f f' : T ⟶ G.X ⊗ H.X)
    (he : f ≫ (G.X ◁ p.hom.hom) = f' ≫ (G.X ◁ p.hom.hom)) :
    f ≫ differenceLift a j p hker hQ = f' ≫ differenceLift a j p hker hQ := by
  apply (cancel_mono j.hom.hom).mp
  have hg := congrArg (fun z => z ≫ fst G.X Q.X) he
  have hx := congrArg (fun z => z ≫ snd G.X Q.X) he
  simp only [Category.assoc, whiskerLeft_fst] at hg
  simp only [Category.assoc, whiskerLeft_snd] at hx
  have e := difference_eq_of_comp_eq a j p hker hN
    (f ≫ fst G.X H.X) (f ≫ snd G.X H.X) (f' ≫ snd G.X H.X) hx
  rw [← lift_differenceLift_comp a j p hker hQ,
    ← lift_differenceLift_comp a j p hker hQ, lift_comp_fst_snd, hg,
    lift_comp_fst_snd] at e
  exact e

/-- The same coequalizing relation on underlying scheme morphisms. -/
theorem differenceLift_eq_of_scheme_comp_eq {Z : Scheme.{u}}
    (f f' : Z ⟶ (G.X ⊗ H.X).left)
    (he : f ≫ (G.X ◁ p.hom.hom).left = f' ≫ (G.X ◁ p.hom.hom).left) :
    f ≫ (differenceLift a j p hker hQ).left =
      f' ≫ (differenceLift a j p hker hQ).left := by
  have hs : f' ≫ (G.X ⊗ H.X).hom = f ≫ (G.X ⊗ H.X).hom := by
    rw [← Over.w (G.X ◁ p.hom.hom), ← Category.assoc, ← he, Category.assoc]
  let f₀ : Over.mk (f ≫ (G.X ⊗ H.X).hom) ⟶ G.X ⊗ H.X := Over.homMk f rfl
  let f₁ : Over.mk (f ≫ (G.X ⊗ H.X).hom) ⟶ G.X ⊗ H.X := Over.homMk f' hs
  exact congrArg (fun z => z.left)
    (differenceLift_eq_of_comp_eq a j p hker hQ hN f₀ f₁ (Over.OverMorphism.ext he))

variable [QuasiCompact p.hom.hom.left] [Flat p.hom.hom.left] [Surjective p.hom.hom.left]

/-- Descent of the kernel-valued difference along the fpqc cover `G × p`. -/
def centralDifferenceSchemeHom : (G.X ⊗ Q.X).left ⟶ N.X.left :=
  haveI := Dynamic.flagQuotient_effectiveEpi_whiskerLeft H p.hom.hom G.X
  EffectiveEpi.desc (G.X ◁ p.hom.hom).left (differenceLift a j p hker hQ).left
    (fun f f' he => differenceLift_eq_of_scheme_comp_eq a j p hker hQ hN f f' he)

@[reassoc]
theorem fac_centralDifferenceSchemeHom :
    (G.X ◁ p.hom.hom).left ≫ centralDifferenceSchemeHom a j p hker hQ hN =
      (differenceLift a j p hker hQ).left :=
  haveI := Dynamic.flagQuotient_effectiveEpi_whiskerLeft H p.hom.hom G.X
  EffectiveEpi.fac _ _ _

/-- The difference family `G × Q → N`, with values on lifted points `x⁻¹ a(g,x)`. -/
def centralDifference : G.X ⊗ Q.X ⟶ N.X :=
  Over.homMk (centralDifferenceSchemeHom a j p hker hQ hN) (by
    have := Dynamic.flagQuotient_effectiveEpi_whiskerLeft H p.hom.hom G.X
    apply (cancel_epi (G.X ◁ p.hom.hom).left).mp
    rw [fac_centralDifferenceSchemeHom_assoc, Over.w, Over.w])

@[reassoc]
theorem fac_centralDifference :
    (G.X ◁ p.hom.hom) ≫ centralDifference a j p hker hQ hN =
      differenceLift a j p hker hQ :=
  Over.OverMorphism.ext (fac_centralDifferenceSchemeHom a j p hker hQ hN)

/-- Evaluation on points of the quotient with a chosen lift. -/
theorem lift_centralDifference_comp {T : Over S} (g : T ⟶ G.X) (x : T ⟶ H.X) :
    (lift g (x ≫ p.hom.hom) ≫ centralDifference a j p hker hQ hN) ≫ j.hom.hom =
      x⁻¹ * a.act g x := by
  rw [← lift_whiskerLeft_assoc, fac_centralDifference, lift_differenceLift_comp]

/-- Naturality of the descended family on every test scheme. -/
theorem centralDifference_naturality {T V : Over S} (b : V ⟶ T)
    (g : T ⟶ G.X) (x : T ⟶ Q.X) :
    b ≫ (lift g x ≫ centralDifference a j p hker hQ hN) =
      lift (b ≫ g) (b ≫ x) ≫ centralDifference a j p hker hQ hN := by
  rw [← Category.assoc, comp_lift]

/-- The family is trivial at the identity of the acting group. -/
theorem one_centralDifference {T : Over S} (x : T ⟶ Q.X) :
    lift (1 : T ⟶ G.X) x ≫ centralDifference a j p hker hQ hN = 1 := by
  apply hom_ext_of_local_quotient_lift p x
  intro V b y hy
  rw [centralDifference_naturality, MonObj.comp_one, MonObj.comp_one, hy]
  apply (cancel_mono j.hom.hom).mp
  rw [lift_centralDifference_comp, a.act_one_left, inv_mul_cancel, MonObj.one_comp]

variable (hc : IsCentral j)

include hc

omit [Mono j.hom.hom] hN [QuasiCompact p.hom.hom.left] [Flat p.hom.hom.left]
    [Surjective p.hom.hom.left] in
/-- Centrality makes the original difference multiplicative in the acted-on point. -/
theorem difference_mul {T : Over S} (g : T ⟶ G.X) (x y : T ⟶ H.X) :
    (x * y)⁻¹ * a.act g (x * y) =
      (x⁻¹ * a.act g x) * (y⁻¹ * a.act g y) := by
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp (difference_mem_range a j p hker hQ g x)
  have hz : Commute (x⁻¹ * a.act g x) y⁻¹ := by
    rw [← hn]
    exact commute_of_mem_center (hc T n) _
  calc
    (x * y)⁻¹ * a.act g (x * y) = y⁻¹ * (x⁻¹ * a.act g x) * a.act g y := by
      rw [a.act_mul_right]; group
    _ = (x⁻¹ * a.act g x) * y⁻¹ * a.act g y := by rw [hz.eq]
    _ = (x⁻¹ * a.act g x) * (y⁻¹ * a.act g y) := by group

/-- The descended difference is a homomorphism in the quotient point, including
points that have no lift over the original test scheme. -/
theorem centralDifference_mul {T : Over S} (g : T ⟶ G.X) (x y : T ⟶ Q.X) :
    lift g (x * y) ≫ centralDifference a j p hker hQ hN =
      (lift g x ≫ centralDifference a j p hker hQ hN) *
        (lift g y ≫ centralDifference a j p hker hQ hN) := by
  apply hom_ext_of_local_quotient_lift p x
  intro V b x' hx
  simp only [centralDifference_naturality, MonObj.comp_mul, hx]
  apply hom_ext_of_local_quotient_lift p (b ≫ y)
  intro W c y' hy
  simp only [centralDifference_naturality, MonObj.comp_mul, hy]
  simp only [← Category.assoc]
  apply (cancel_mono j.hom.hom).mp
  rw [MonObj.mul_comp, ← MonObj.mul_comp (c ≫ x') y' p.hom.hom, lift_centralDifference_comp,
    lift_centralDifference_comp, lift_centralDifference_comp,
    difference_mul a j p hker hQ hc]

end Langlands.GroupScheme.AutomorphicAction
