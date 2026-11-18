import Langlands.GroupScheme.HomScheme.SquareZeroCohomologyStatement
import Langlands.GroupScheme.HomScheme.SquareZeroSchemeLift
import Langlands.GroupScheme.Cohomology.SourceTransport
import Langlands.GroupScheme.RelativeLevi.ModuliTrivialization
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Reduction of the relative square-zero bridge to affine bases

The relative statement `SquareZeroHomomorphismCohomologyStatement` (arbitrary base `S`, a
square-zero thickening `Spec (A ⧸ I) ⟶ Spec A ⟶ S`) follows from its absolute form over affine
bases `Spec R`, by base change of the groups to `Spec A`, the identification of iterated base
changes, and lifting of prescribed conjugators by smoothness of the target.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

/-- The absolute square-zero deformation bridge over affine bases: for an affine flat source and
a smooth target over `Spec R`, a square-zero ideal `I` and low-degree cohomology vanishing of the
reduced source, homomorphisms over `R ⧸ I` lift, and lifts agreeing over `R ⧸ I` are conjugate
by a point of `G(R)` reducing to `1`. -/
def AbsoluteSquareZeroCohomologyLiftStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (I : Ideal R)
    [Fact (Langlands.AlgebraicGeometry.SmoothLifting.SqZero I)]
    (H G : GroupScheme (Spec R)) [IsAffineHom H.X.hom] [Flat H.X.hom] [Smooth G.X.hom],
    Cohomology.HasVanishingLowDegreeCohomology
      ((baseChange (Spec.algebraMap R (R ⧸ I))).obj H) →
    (∀ f₀ : (baseChange (Spec.algebraMap R (R ⧸ I))).obj H ⟶
        (baseChange (Spec.algebraMap R (R ⧸ I))).obj G,
      ∃ f : H ⟶ G, (baseChange (Spec.algebraMap R (R ⧸ I))).map f = f₀) ∧
    (∀ f f' : H ⟶ G, (baseChange (Spec.algebraMap R (R ⧸ I))).map f =
        (baseChange (Spec.algebraMap R (R ⧸ I))).map f' →
      ∃ g : Over.mk (𝟙 (Spec R)) ⟶ G.X,
        G.constantPoint g (Over.mk (Spec.algebraMap R (R ⧸ I))) = 1 ∧
          f' = f ≫ (G.innerIso g).hom)

theorem sqZero_of_sq_eq_bot {A : Type u} [CommRing A] {I : Ideal A} (hI : I ^ 2 = ⊥) :
    Langlands.AlgebraicGeometry.SmoothLifting.SqZero I := fun a ha b hb => by
  have h : a * b ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
  rw [hI] at h
  exact (Submodule.mem_bot A).mp h

/-- Evaluation along a test morphism given by a scheme map is the pullback of homomorphisms
through the iterated base change comparison. -/
theorem evaluate_homMk {S U X : Scheme.{u}} {H G : GroupScheme S} (a : X ⟶ S) (q : U ⟶ X)
    (i : RelativeHom H G (Over.mk a)) :
    evaluate (Over.homMk q rfl : Over.mk (q ≫ a) ⟶ Over.mk a) i =
      (Descent.pullbackComparison a q (q ≫ a) rfl H).inv ≫ (baseChange q).map i ≫
        (Descent.pullbackComparison a q (q ≫ a) rfl G).hom :=
  rfl

set_option maxHeartbeats 1600000 in
/-- **Relative reduction of the square-zero bridge.** The absolute statement over affine bases
implies the relative statement over arbitrary bases. -/
theorem squareZeroCohomology_of_absolute
    (habs : AbsoluteSquareZeroCohomologyLiftStatement.{u}) :
    SquareZeroHomomorphismCohomologyStatement.{u} := by
  intro S H G _ A _ I hI a b w hflat haff hvan
  subst w
  have : Fact (Langlands.AlgebraicGeometry.SmoothLifting.SqZero I) := ⟨sqZero_of_sq_eq_bot hI⟩
  have : IsAffine ((baseChange a).obj H).X.left := haff
  have : Flat ((baseChange a).obj H).X.hom := hflat
  have : Smooth ((baseChange a).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom a)
    infer_instance
  have hvan' := Cohomology.HasVanishingLowDegreeCohomology.of_iso
    (Descent.pullbackComparison a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) _ rfl H)
    hvan
  obtain ⟨hlift, hconj⟩ := habs (CommRingCat.of A) I ((baseChange a).obj H)
    ((baseChange a).obj G) hvan'
  have hlift' : ∀ f₀ : (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((baseChange a).obj H) ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((baseChange a).obj G),
      ∃ f : (baseChange a).obj H ⟶ (baseChange a).obj G,
        (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f = f₀ :=
    hlift
  have hconj' : ∀ f f' : (baseChange a).obj H ⟶ (baseChange a).obj G,
      (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f =
        (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f' →
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ ((baseChange a).obj G).X,
        ((baseChange a).obj G).constantPoint g
          (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) = 1 ∧
          f' = f ≫ (((baseChange a).obj G).innerIso g).hom :=
    hconj
  constructor
  · intro i₀
    obtain ⟨f, hf⟩ := hlift'
      ((Descent.pullbackComparison a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) _
          rfl H).hom ≫ i₀ ≫
        (Descent.pullbackComparison a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) _
          rfl G).inv)
    refine ⟨f, ?_⟩
    rw [evaluate_homMk, hf]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · intro i j g₀ h
    have hK : Langlands.AlgebraicGeometry.SmoothLifting.SqZero
        (RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk I)).hom) := by
      rw [CommRingCat.hom_ofHom, Ideal.mk_ker]
      exact sqZero_of_sq_eq_bot hI
    obtain ⟨x, hx₀, hxs⟩ := Langlands.AlgebraicGeometry.SmoothLifting.exists_lift_sqZero
      (f := G.X.hom) (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective hK
      g₀.left a (Over.w g₀)
    let g₁ : Over.mk a ⟶ G.X := Over.homMk x hxs
    have hg₁ : (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a) ⟶ Over.mk a) ≫ g₁ =
          g₀ :=
      Over.OverMorphism.ext hx₀
    have he : evaluate (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a) ⟶ Over.mk a)
          (conjugateRelative i g₁) =
        evaluate (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a) ⟶ Over.mk a) j := by
      rw [evaluate_conjugateRelative, hg₁, h]
    rw [evaluate_homMk, evaluate_homMk] at he
    have hbc := (cancel_mono _).mp ((cancel_epi _).mp he)
    obtain ⟨g₂, hg₂1, hg₂⟩ := hconj' (conjugateRelative i g₁) j hbc
    let g₂' := (RelativeLevi.pulledBackPointEquiv G (Over.mk a)).symm g₂
    have hpb : RelativeLevi.pulledBackPoint G (Over.mk a) g₂' = g₂ :=
      (RelativeLevi.pulledBackPointEquiv G (Over.mk a)).apply_symm_apply g₂
    refine ⟨g₂' * g₁, ?_, ?_⟩
    · have e : baseChangePointsEquiv a G
          (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
          (((baseChange a).obj G).constantPoint g₂
            (Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) =
          (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :
            Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a) ⟶ Over.mk a) ≫
              g₂' := by
        apply Over.OverMorphism.ext
        rw [baseChangePointsEquiv_left, ← hpb]
        change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
            (RelativeLevi.pulledBackPoint G (Over.mk a) g₂').left) ≫
              pullback.fst G.X.hom a = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g₂'.left
        exact (Category.assoc _ _ _).trans (congrArg
          (fun k => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ k)
          (pullback.lift_fst _ _ _))
      rw [MonObj.comp_mul, hg₁, ← e, hg₂1, map_one, one_mul]
    · change j = i ≫ (((baseChange a).obj G).innerIso
        (RelativeLevi.pulledBackPoint G (Over.mk a) (g₂' * g₁))).hom
      rw [show RelativeLevi.pulledBackPoint G (Over.mk a) (g₂' * g₁) =
          RelativeLevi.pulledBackPoint G (Over.mk a) g₂' *
            RelativeLevi.pulledBackPoint G (Over.mk a) g₁ from
        map_mul (RelativeLevi.pulledBackPointHom G (Over.mk a)) g₂' g₁,
        innerIso_mul_hom, hpb, ← Category.assoc]
      exact hg₂

end Langlands.GroupScheme.HomScheme
