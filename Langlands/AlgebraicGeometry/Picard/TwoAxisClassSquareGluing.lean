import Langlands.AlgebraicGeometry.Picard.TwoAxisClassArtinianLiftingProof

/-! # Gluing two-axis classes along ring pullback squares -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AbelianScheme

namespace TwoAxisRigidifiedLineBundle

open TwoAxisFamily UnramifiedFunctor

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)
variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

section SquareGluing

variable {R A' B' C : Type u} [CommRing R] [Algebra Λ R] [CommRing A'] [Algebra Λ A']
  [CommRing B'] [Algebra Λ B'] [CommRing C] [Algebra Λ C]
  (p : R →ₐ[Λ] A') (q : R →ₐ[Λ] B') (a : A' →ₐ[Λ] C) (b : B' →ₐ[Λ] C)

/-- Line-bundle gluing along a ring pullback square `R = A' ×_C B'` of `Λ`-algebras whose
leg `b : B' → C` is surjective with nilpotent kernel: a line bundle `D` on the self-product
over `A'` and a line bundle `L` on the self-product over `B'` that agree over `C` come from a
line bundle on the self-product over `R` whose restriction along `p` is `D`. -/
theorem exists_squareExtension
    (hsq : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom))
    (D : LineBundle (mumfordProduct (abelian A (algebraOver f A'))).left)
    (L : LineBundle (mumfordProduct (abelian A (algebraOver f B'))).left)
    (φ : (LineBundle.pullback (productMap A (algHomOver f b))).obj L ≅
      (LineBundle.pullback (productMap A (algHomOver f a))).obj D) :
    ∃ E : LineBundle (mumfordProduct (abelian A (algebraOver f R))).left,
      Nonempty ((LineBundle.pullback (productMap A (algHomOver f p))).obj E ≅ D) := by
  have := FlatInfinitesimalGluing.affineSquareComparison_isEquivalence (productStructure A f)
    p q a b hsq hb hn
  let e : (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap a))).obj
        ((LineBundle.pullback (inv (affineComparison A f A'))).obj D) ≅
      (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap b))).obj
        ((LineBundle.pullback (inv (affineComparison A f B'))).obj L) :=
    LineBundle.pullbackCompEqIso ((relativeSpace (productStructure A f)).map
        (affineBaseMap a))
      (inv (affineComparison A f A')) (inv_affineComparison_naturality A f _) D ≪≫
    (LineBundle.pullbackCompEqIso (inv (affineComparison A f C))
      (productMap A (algHomOver f a)) rfl D).symm ≪≫
    (LineBundle.pullback (inv (affineComparison A f C))).mapIso φ.symm ≪≫
    LineBundle.pullbackCompEqIso (inv (affineComparison A f C))
      (productMap A (algHomOver f b)) rfl L ≪≫
    (LineBundle.pullbackCompEqIso ((relativeSpace (productStructure A f)).map
        (affineBaseMap b))
      (inv (affineComparison A f B')) (inv_affineComparison_naturality A f _) L).symm
  let Dat : PicardGroupoid.SquareGluingData
      ((relativeSpace (productStructure A f)).map (affineBaseMap a))
      ((relativeSpace (productStructure A f)).map (affineBaseMap b)) :=
    { left := ⟨(LineBundle.pullback (inv (affineComparison A f A'))).obj D⟩
      right := ⟨(LineBundle.pullback (inv (affineComparison A f B'))).obj L⟩
      hom := ⟨e⟩ }
  obtain ⟨Z, ⟨eZ⟩⟩ := Functor.EssSurj.mem_essImage
    (PicardGroupoid.affineSquareComparison (productStructure A f) p q a b hsq) Dat
  let eZl : (LineBundle.pullback ((relativeSpace (productStructure A f)).map
        (affineBaseMap p))).obj Z.of ≅
      (LineBundle.pullback (inv (affineComparison A f A'))).obj D :=
    eZ.hom.left.iso
  refine ⟨(LineBundle.pullback (affineComparison A f R)).obj Z.of, ⟨?_⟩⟩
  exact LineBundle.pullbackCompEqIso (productMap A (algHomOver f p))
      (affineComparison A f R) (affineComparison_naturality A f p).symm Z.of ≪≫
    (LineBundle.pullbackCompEqIso (affineComparison A f A')
      ((relativeSpace (productStructure A f)).map (affineBaseMap p))
      rfl Z.of).symm ≪≫
    (LineBundle.pullback (affineComparison A f A')).mapIso eZl ≪≫
    LineBundle.pullbackCompEqIso (affineComparison A f A') (inv (affineComparison A f A'))
      (IsIso.hom_inv_id _) D ≪≫
    (LineBundle.pullbackId _).app D

/-- Class-level gluing along a ring pullback square `R = A' ×_C B'` of `Λ`-algebras whose
leg `b : B' → C` is surjective with nilpotent kernel: a class over `A'` and a class over `B'`
with the same restriction to `C` come from a class over `R`, whose restriction along `p` is
the given class over `A'`. -/
theorem classes_squareGluing
    (hsq : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
      (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hb : Function.Surjective b) (hn : IsNilpotent (RingHom.ker b.toRingHom))
    (x : Classes A (algebraOver f A')) (y : Classes A (algebraOver f B'))
    (hxy : classesPullback A (algHomOver f b) y = classesPullback A (algHomOver f a) x) :
    ∃ z : Classes A (algebraOver f R), classesPullback A (algHomOver f p) z = x := by
  induction x using Quotient.inductionOn with
  | h D₀ =>
  induction y using Quotient.inductionOn with
  | h L' =>
  have hxy' : (Quotient.mk _ ((relativePullback A (algHomOver f b)).obj L') :
        Classes A (algebraOver f C)) =
      Quotient.mk _ ((relativePullback A (algHomOver f a)).obj D₀) :=
    hxy
  obtain ⟨φ⟩ := Quotient.exact hxy'
  obtain ⟨E₀, ⟨e₀⟩⟩ := exists_squareExtension A f p q a b hsq hb hn
    ⟨D₀.obj.carrier, D₀.property⟩ ⟨L'.obj.carrier, L'.property⟩
    ((forget _ _ _ _ _).mapIso φ)
  let ρ := LineBundle.twoAxisNormalizedBundleRigidification pullbackTensorComparisonIsIso
    (abelian A (algebraOver f R)) E₀
  let eN := LineBundle.twoAxisNormalizedBundleRestrictionIso pullbackTensorComparisonIsIso
    (abelian A (algebraOver f R)) (abelian A (algebraOver f A'))
    (productMap A (algHomOver f p)) (carrierMap A (algHomOver f p))
    (productMap_fst A _) (productMap_snd A _) (first_naturality A _) (second_naturality A _)
    E₀ ⟨D₀.obj.carrier, D₀.property⟩ ((LineBundle.forget _).mapIso e₀)
    D₀.obj.rigidification.first.symm D₀.obj.rigidification.second.symm
  refine ⟨Quotient.mk _ (ofLineBundle _ ρ), ?_⟩
  change (Quotient.mk _ ((relativePullback A (algHomOver f p)).obj (ofLineBundle _ ρ)) :
      Classes A (algebraOver f A')) = Quotient.mk _ D₀
  exact Quotient.sound (nonempty_iso_of_carrierIso (abelian A (algebraOver f A')) eN)

end SquareGluing

end TwoAxisRigidifiedLineBundle

end Langlands.AlgebraicGeometry.Picard
