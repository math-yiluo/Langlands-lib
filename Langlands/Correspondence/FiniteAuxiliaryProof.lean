import Langlands.Correspondence.FiniteAuxiliaryStatement

/-!
# Finite auxiliary arguments for constructing correspondences

The six elementary components are proved without any representation-theoretic
assumption beyond the explicit hypotheses of their published statements.
-/

namespace Langlands.Henniart

universe uX uY uT uS uR uI uU uF uK

theorem finiteSeparation (X : Type uX) (T : Type uT) (R : Type uR) :
    FiniteSeparationStatement X T R := by
  classical
  intro P hP evaluate hseparate
  let := hP.fintype
  let pairs := {p : P × P // p.1.val ≠ p.2.val}
  let pick : pairs → T := fun p =>
    Classical.choose (hseparate p.1.1 p.1.1.property p.1.2 p.1.2.property p.2)
  refine ⟨Finset.univ.image pick, ?_⟩
  intro x hx y hy hequal
  by_contra hxy
  let p : pairs := ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
  have hp : pick p ∈ Finset.univ.image pick :=
    Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  exact (Classical.choose_spec (hseparate x hx y hy hxy)) (hequal (pick p) hp)

theorem finiteTestLifting (S : Type uS) (T : Type uT) :
    FiniteTestLiftingStatement S T := by
  classical
  intro tests project hpreimage
  let lift : tests → S := fun t => Classical.choose (hpreimage t t.property)
  have hlift (t : tests) : project (lift t) = t :=
    Classical.choose_spec (hpreimage t t.property)
  refine ⟨Finset.univ.image lift, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
    rw [hlift]
    exact t.property
  · intro t ht
    let a : tests := ⟨t, ht⟩
    exact ⟨lift a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, hlift a⟩

theorem finiteLiftedSeparation
    (X : Type uX) (S : Type uS) (T : Type uT) (R : Type uR) :
    FiniteLiftedSeparationStatement X S T R := by
  intro P evaluate tests project hseparate hpreimage
  obtain ⟨lifts, hmaps, hcover⟩ := finiteTestLifting S T tests project hpreimage
  refine ⟨lifts, hmaps, ?_⟩
  intro x hx y hy hequal
  apply hseparate x hx y hy
  intro t ht
  obtain ⟨s, hs, hst⟩ := hcover t ht
  simpa only [hst] using hequal s hs

theorem finiteGaloisEnlargement
    (F : Type uF) (K : Type uK) [Field F] [Field K] [Algebra F K] :
    FiniteGaloisEnlargementStatement F K := by
  classical
  intro fields hfields
  let : ∀ E : fields, FiniteDimensional F E.val :=
    fun E => (hfields E E.property).1
  let : ∀ E : fields, IsGalois F E.val :=
    fun E => (hfields E E.property).2
  let L : IntermediateField F K := ⨆ E : fields, E.val
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  intro E hE
  exact le_iSup (fun E : fields => E.val) ⟨E, hE⟩

theorem finiteCounting (X : Type uX) (Y : Type uY) :
    FiniteCountingStatement X Y := by
  intro f A B _hA hB hcard hinj hmaps y hy
  obtain ⟨x, hx, hxy⟩ :=
    Set.surj_on_of_inj_on_of_ncard_le (fun a (_ : a ∈ A) => f a)
      (fun a ha => hmaps ha)
      (fun a b ha hb hab => hinj ha hb hab) hcard.ge hB y hy
  exact ⟨x, hx, hxy.symm⟩

theorem finiteOrbitCounting
    (U : Type uU) (X : Type uX) (Y : Type uY) (I : Type uI)
    [Group U] [MulAction U X] [MulAction U Y] :
    FiniteOrbitCountingStatement U X Y I := by
  intro f hinj hequivariant source target hfinite hmaps horbit y
  obtain ⟨u, i, hy⟩ := horbit y
  obtain ⟨x, _, hxy⟩ :=
    finiteCounting X Y f (source i) (target i)
      (hfinite i).1 (hfinite i).2.1 (hfinite i).2.2 hinj.injOn (hmaps i) hy
  refine ⟨u⁻¹ • x, ?_⟩
  rw [hequivariant, hxy, inv_smul_smul]

theorem finiteAuxiliary
    (X : Type uX) (Y : Type uY) (T : Type uT) (S : Type uS) (R : Type uR)
    (I : Type uI) (U : Type uU) (F : Type uF) (K : Type uK)
    [Group U] [MulAction U X] [MulAction U Y]
    [Field F] [Field K] [Algebra F K] :
    FiniteAuxiliaryStatement X Y T S R I U F K :=
  ⟨finiteSeparation X T R, finiteTestLifting S T, finiteLiftedSeparation X S T R,
    finiteGaloisEnlargement F K, finiteCounting X Y, finiteOrbitCounting U X Y I⟩

end Langlands.Henniart
