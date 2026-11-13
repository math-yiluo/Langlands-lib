import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Smooth.JordanHolderGrothendieck
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.MultiplicityIndependenceProof

/-!
# Identifying an irreducible head by a positive Jacquet count

If an irreducible quotient `P` of a representation `X` with the same composition
factors as `I` has a positive count of a test representation `τ` after an
injection- and surjection-preserving functor `J`, while `J(I)` has total count
`m` and the irreducible quotient `L` of `I` already has count at least `m`, then
`P ≅ L`.
-/

noncomputable section

namespace Langlands.Classification.HeadDetectingCount

open CategoryTheory SmoothRep SmoothRep.IrreducibleGrothendieckProof
open Langlands.VirtualRepresentation

universe uK uG uV uH uW uT uA uB uC

section Counts

variable {k : Type uK} [Field k] {H : Type uH} [Monoid H]

/-- A representation embedded in one with a finite composition series has one,
with no larger count of any given representation. -/
theorem exists_count_le_of_injective {A : Rep.{uA} k H} {B : Rep.{uB} k H}
    (τ : Rep.{uT} k H) (i : A.ρ.IntertwiningMap B.ρ) (hi : Function.Injective i)
    {mB : ℕ} (hB : HasJordanHolderMultiplicity B τ mB) :
    ∃ mA, HasJordanHolderMultiplicity A τ mA ∧ mA ≤ mB := by
  let W : Submodule k B := LinearMap.range i.toLinearMap
  have hW : ∀ g, W ≤ W.comap (B.ρ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, Representation.IntertwiningMap.isIntertwining _ _ i g v⟩
  let Q : Rep.{uB} k H := Rep.of (B.ρ.quotient W hW)
  let qQ : B.ρ.IntertwiningMap Q.ρ :=
    { toLinearMap := W.mkQ
      isIntertwining' := fun _ => rfl }
  obtain ⟨a, c, ha, -, hac⟩ :=
    jordanHolderShortExactDecomposition k H A B Q τ i qQ hi (W.mkQ_surjective)
      (Submodule.ker_mkQ W).symm mB hB
  exact ⟨a, ha, by omega⟩

/-- A quotient of a representation with a finite composition series has one,
with no larger count of any given representation. -/
theorem exists_count_le_of_surjective {B : Rep.{uB} k H} {C : Rep.{uC} k H}
    (τ : Rep.{uT} k H) (q : B.ρ.IntertwiningMap C.ρ) (hq : Function.Surjective q)
    {mB : ℕ} (hB : HasJordanHolderMultiplicity B τ mB) :
    ∃ mC, HasJordanHolderMultiplicity C τ mC ∧ mC ≤ mB := by
  let K : Rep.{uB} k H := Rep.of q.ker.toRepresentation
  let iK : K.ρ.IntertwiningMap B.ρ :=
    { toLinearMap := q.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  obtain ⟨a, c, -, hc, hac⟩ :=
    jordanHolderShortExactDecomposition k H K B C τ iK q
      (Submodule.injective_subtype _) hq (Submodule.range_subtype _) mB hB
  exact ⟨c, hc, by omega⟩

end Counts

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Irreducible subquotients transfer along matching composition factors. -/
theorem isSubquotient_of_haveSameJordanHolderFactors
    {X I P : SmoothRep.{uK, uG, uV} k G} (hX : X.HasFiniteLength)
    (hI : I.HasFiniteLength) (h : HaveSameJordanHolderFactors X.obj I.obj)
    (hP : P.IsIrreducible) (hsub : IsSubquotient P X) : IsSubquotient P I := by
  have hclass := FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_haveSameJordanHolderFactors
    hX hI h
  exact hasConstituentSupportIn_of_class_natural_multiple ⟨X, hX⟩ ⟨I, hI⟩ 1
    (by rw [one_smul]; exact hclass) P hP hsub

/-- An irreducible subquotient of `I` which is not isomorphic to the irreducible
quotient `L` of `I` is a subquotient of the kernel of the quotient map. -/
theorem isSubquotient_kernel_of_not_iso
    {I L P : SmoothRep.{uK, uG, uV} k G} (hI : I.HasFiniteLength)
    (q : I ⟶ L) (hq : Function.Surjective (hom q)) (hL : L.IsIrreducible)
    (hP : P.IsIrreducible) (hsub : IsSubquotient P I) (hne : ¬ Nonempty (P ≅ L)) :
    IsSubquotient P (kernel q) := by
  classical
  have hK : (kernel q).HasFiniteLength := subrepresentation_hasFiniteLength hI _
  have hLf : L.HasFiniteLength := hasFiniteLength_of_isIrreducible hL
  have hses : IsShortExact (hom (kernelι q)) (hom q) :=
    ⟨subtype_injective I _, hq, Submodule.range_subtype _⟩
  have hsum := compositionFactors_shortExact ⟨kernel q, hK⟩ ⟨I, hI⟩ ⟨L, hLf⟩
    (hom (kernelι q)) (hom q) hses
  have hcoord := congrArg (fun v => v (irreducibleIsoClass P hP)) hsum
  simp only [Finsupp.add_apply] at hcoord
  rw [compositionFactors_irreducible L hL hLf, compositionFactors_apply,
    compositionFactors_apply] at hcoord
  have hgen : (generator (irreducibleIsoClass L hL) :
      IrreducibleLattice.{uK, uG, uV} k G) (irreducibleIsoClass P hP) = 0 := by
    unfold generator
    apply Finsupp.single_eq_of_ne
    intro heq
    exact hne ((irreducibleIsoClass_eq_iff hP hL).mp heq)
  rw [hgen, add_zero] at hcoord
  have hpos := (compositionMultiplicity_pos_iff_isSubquotient ⟨I, hI⟩ P hP).mpr hsub
  have hposK : 0 < compositionMultiplicity ⟨kernel q, hK⟩ P := by
    have := hcoord
    omega
  exact (compositionMultiplicity_pos_iff_isSubquotient ⟨kernel q, hK⟩ P hP).mp hposK

variable {H : Type uH} [Monoid H]

/-- An irreducible subquotient of the kernel of `q : I ↠ L` has zero count when
the count of `L` is at least the count of `I`. -/
theorem false_of_kernel_count
    (J : SmoothRep.{uK, uG, uV} k G ⥤ Rep.{uW} k H) [J.PreservesZeroMorphisms]
    (hJinj : ∀ {A B : SmoothRep.{uK, uG, uV} k G} (f : A ⟶ B),
      Function.Injective (hom f) → Function.Injective (J.map f).hom)
    (hJsurj : ∀ {A B : SmoothRep.{uK, uG, uV} k G} (f : A ⟶ B),
      Function.Surjective (hom f) → Function.Surjective (J.map f).hom)
    {I L P : SmoothRep.{uK, uG, uV} k G} (q : I ⟶ L)
    (hq : Function.Surjective (hom q)) (τ : Rep.{uT} k H) (m : ℕ)
    (hIm : HasJordanHolderMultiplicity (J.obj I) τ m)
    (hLm : ∃ c, m ≤ c ∧ HasJordanHolderMultiplicity (J.obj L) τ c)
    (hPc : ∃ c, 0 < c ∧ HasJordanHolderMultiplicity (J.obj P) τ c)
    (hsub : IsSubquotient P (kernel q)) : False := by
  obtain ⟨c, hmc, hLc⟩ := hLm
  obtain ⟨c', hc', hPc'⟩ := hPc
  -- the kernel of `J q` has zero count
  let f := (J.map q).hom
  have hf : Function.Surjective f := hJsurj q hq
  let K : Rep.{uW} k H := Rep.of f.ker.toRepresentation
  let iK : K.ρ.IntertwiningMap (J.obj I).ρ :=
    { toLinearMap := f.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  obtain ⟨a, c₁, ha, hc₁, hac⟩ :=
    jordanHolderShortExactDecomposition k H K (J.obj I) (J.obj L) τ iK f
      (Submodule.injective_subtype _) hf (Submodule.range_subtype _) m hIm
  have hc₁c := HasJordanHolderMultiplicity.unique hc₁ hLc
  -- the subquotient presentation inside the kernel of `q`
  obtain ⟨C, i, p, hi, hp⟩ := isSubquotient_iff_exists.mp hsub
  let j : C ⟶ I := i ≫ kernelι q
  have hj : Function.Injective (hom j) := by
    rw [SmoothRep.hom_comp]
    exact (subtype_injective I _).comp hi
  have hjq : j ≫ q = 0 := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    ext v
    change (hom q) ((hom (kernelι q)) ((hom i) v)) = 0
    exact ((hom i) v).property
  have hJjq (v : J.obj C) : f ((J.map j).hom v) = 0 := by
    have h0 : J.map j ≫ J.map q = 0 := by
      rw [← J.map_comp, hjq, Functor.map_zero]
    exact congrArg (fun g => g.hom v) h0
  -- `J C` embeds in the kernel of `J q`
  let g : (J.obj C).ρ.IntertwiningMap K.ρ :=
    { toLinearMap := (J.map j).hom.toLinearMap.codRestrict f.ker.toSubmodule hJjq
      isIntertwining' := fun h => by
        ext v
        exact Rep.hom_comm_apply (J.map j) h v }
  have hg : Function.Injective g := fun v w hvw =>
    hJinj j hj (congrArg Subtype.val hvw)
  obtain ⟨mC, hmC, hmCa⟩ := exists_count_le_of_injective τ g hg ha
  obtain ⟨mP, hmP, hmPC⟩ :=
    exists_count_le_of_surjective τ (J.map p).hom (hJsurj p hp) hmC
  have := HasJordanHolderMultiplicity.unique hPc' hmP
  omega

/-- An irreducible quotient `P` of a representation with the same composition
factors as `I` is isomorphic to the irreducible quotient `L` of `I`, as soon as
`P` has a positive count after `J` and `L` has a count after `J` at least the
count of `J I`. -/
theorem nonempty_iso_of_count
    (J : SmoothRep.{uK, uG, uV} k G ⥤ Rep.{uW} k H) [J.PreservesZeroMorphisms]
    (hJinj : ∀ {A B : SmoothRep.{uK, uG, uV} k G} (f : A ⟶ B),
      Function.Injective (hom f) → Function.Injective (J.map f).hom)
    (hJsurj : ∀ {A B : SmoothRep.{uK, uG, uV} k G} (f : A ⟶ B),
      Function.Surjective (hom f) → Function.Surjective (J.map f).hom)
    {X I L P : SmoothRep.{uK, uG, uV} k G} (hX : X.HasFiniteLength)
    (hI : I.HasFiniteLength) (hXI : HaveSameJordanHolderFactors X.obj I.obj)
    (q : I ⟶ L) (hq : Function.Surjective (hom q)) (hL : L.IsIrreducible)
    (r : X ⟶ P) (hr : Function.Surjective (hom r)) (hP : P.IsIrreducible)
    (τ : Rep.{uT} k H) (m : ℕ)
    (hIm : HasJordanHolderMultiplicity (J.obj I) τ m)
    (hLm : ∃ c, m ≤ c ∧ HasJordanHolderMultiplicity (J.obj L) τ c)
    (hPc : ∃ c, 0 < c ∧ HasJordanHolderMultiplicity (J.obj P) τ c) :
    Nonempty (P ≅ L) := by
  by_contra hne
  have hPX : IsSubquotient P X :=
    isSubquotient_iff_exists.mpr ⟨X, 𝟙 X, r, fun _ _ h => h, hr⟩
  have hPI := isSubquotient_of_haveSameJordanHolderFactors hX hI hXI hP hPX
  exact false_of_kernel_count J hJinj hJsurj q hq τ m hIm hLm hPc
    (isSubquotient_kernel_of_not_iso hI q hq hL hP hPI hne)

end Langlands.Classification.HeadDetectingCount
