import Langlands.Cohomology.DivisibleSystem.PowTorsionProjective
import Langlands.Cohomology.DivisibleSystem.ProPInvariants

/-!
# Projectivity of permutation modules of pro-`p` subgroups

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
The published module `PowTorsionProjective` reduces the hypothesis `PowTorsionProjective ℓ m`
for compact inductions to the inducing representations, and leaves open whether the trivial
representation of a pro-`p` subgroup has it. On p.305 Harris takes an open normal pro-`p`
subgroup `H ⊂ S(ẽ)` and writes: "Since `p` is prime to `ℓ`, the functor `H⁰(H, •)` is exact on
`ℓ`-primary torsion modules". Taking a form of that exactness as the hypothesis
`hP : ProPInvariantsExactStatement` (Worker 3's proposition, not proved here), this module
shows:

* `smoothTrivialFunctor R K`, `smoothInvariantsFunctor R K` and `smoothTrivialAdjunction R K`:
  the trivial smooth representation of a topological group `K` on an `R`-module is left adjoint
  to the `K`-invariants of smooth representations (Mathlib's `Rep.invariantsAdjunction`,
  restricted to smooth representations);
* `smoothInvariantsFunctor_preservesEpimorphisms`: given `hP`, the invariants of a compact
  totally disconnected group whose quotients by open normal subgroups are `p`-groups preserve
  epimorphisms of smooth representations when `p` is invertible in `R`;
* `projective_smoothTrivialFunctor_obj`, `powTorsionProjective_smoothTrivialFunctor_obj` and
  `projective_smoothTrivialFunctor_obj_of_isProPSubgroup`: hence the trivial representation of
  such a group (or of a pro-`p` subgroup `H`) on a projective `R`-module is projective, and on
  an `R`-module with `PowTorsionProjective ℓ m` it has `PowTorsionProjective ℓ m`;
* `projective_smoothCompactInduction_smoothTrivialFunctor_obj`,
  `powTorsionProjective_compactInduction_smoothTrivialFunctor_obj` and
  `powTorsionProjective_cokernel_compactInduction_smoothTrivialFunctor_obj`: for an open
  pro-`p` subgroup `H` of `G`, compact induction `c-Ind_H^G M` of the trivial representation on
  an `R`-module `M` is projective if `M` is projective and has `PowTorsionProjective ℓ m` if `M`
  has it; for `M` projective, its quotient `c-Ind_H^G M / ℓ^m` (the cokernel of multiplication
  by `ℓ ^ m`) has `PowTorsionProjective ℓ m`.

For `M = R^(I)` free, `c-Ind_H^G M` is the direct sum of `I` copies of the permutation
representation `R[H\G]` on finitely supported functions on the right cosets of `H`; for `H`
normal, this is the free `R[G/H]`-module of rank `I`, and its quotient by `ℓ ^ m` is the free
`R/ℓ^m R[G/H]`-module of rank `I`, the kind of module named by Harris. These identifications are
not formalized here, nor is the fact that Harris's `C^j_m(ẽ)^{H_p}` are such modules.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe uR uK uV uG u

section Trivial

variable (R : Type uR) [CommRing R] (K : Type uK) [Group K] [TopologicalSpace K]

/-- A trivial representation is smooth: the whole group fixes every vector. -/
lemma isSmooth_trivial (M : Type uV) [AddCommGroup M] [Module R M] :
    IsSmooth (Representation.trivial R K M) :=
  fun _ => ⟨⊤, fun _ => rfl⟩

/-- The functor equipping an `R`-module with the trivial smooth representation of `K`. -/
def smoothTrivialFunctor : ModuleCat.{uV} R ⥤ SmoothRep.{uR, uK, uV} R K :=
  (smoothRepProperty R K).lift (Rep.trivialFunctor R K) fun M => isSmooth_trivial R K M

/-- The functor sending a smooth representation of `K` to its `R`-module of `K`-invariants. -/
abbrev smoothInvariantsFunctor : SmoothRep.{uR, uK, uV} R K ⥤ ModuleCat.{uV} R :=
  SmoothRep.toRep ⋙ Rep.invariantsFunctor R K

/-- The trivial smooth representation functor is left adjoint to the invariants functor: a
morphism of smooth representations from the trivial representation on `M` to `A` is an
`R`-linear map from `M` to the `K`-invariants of `A`. This is Mathlib's
`Rep.invariantsAdjunction`, restricted to the full subcategory of smooth representations. -/
def smoothTrivialAdjunction : smoothTrivialFunctor R K ⊣ smoothInvariantsFunctor R K :=
  (Rep.invariantsAdjunction R K).restrictFullyFaithful (iC := 𝟭 (ModuleCat.{uV} R))
    (iD := SmoothRep.toRep) (Functor.FullyFaithful.id _) (smoothRepProperty R K).fullyFaithfulι
    (Functor.leftUnitor _ ≪≫ ((smoothRepProperty R K).liftCompιIso _ _).symm)
    (Functor.rightUnitor _).symm

variable [IsTopologicalGroup K]

/-- Given `ProPInvariantsExactStatement`, the `K`-invariants functor on smooth representations
preserves epimorphisms, for a compact totally disconnected group `K` whose quotients by open
normal subgroups are `p`-groups and `p` invertible in `R`: the kernel short complex of an
epimorphism is short exact, hence so is its image under invariants. -/
theorem smoothInvariantsFunctor_preservesEpimorphisms
    (hP : ProPInvariantsExactStatement.{uK, uR, uV}) {p : ℕ} (hp : p.Prime) [CompactSpace K]
    [TotallyDisconnectedSpace K] (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup))
    (hR : IsUnit (p : R)) :
    (smoothInvariantsFunctor.{uR, uK, uV} R K).PreservesEpimorphisms where
  preserves {A B} f _ := by
    have : (SmoothRep.toRep : SmoothRep.{uR, uK, uV} R K ⥤ _).PreservesHomology :=
      Functor.preservesHomology_of_preservesEpis_and_kernels _
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel f) }
    exact (hP p hp K hK R hR _ (hS.map SmoothRep.toRep) (kernel f).property A.property
      B.property).epi_g

/-- Given `ProPInvariantsExactStatement`, the trivial smooth representation of `K` on a
projective `R`-module `M` is a projective smooth representation, for `K` and `p` as in
`smoothInvariantsFunctor_preservesEpimorphisms`: it is the image of `M` under a left adjoint
whose right adjoint preserves epimorphisms. -/
theorem projective_smoothTrivialFunctor_obj
    (hP : ProPInvariantsExactStatement.{uK, uR, uV}) {p : ℕ} (hp : p.Prime) [CompactSpace K]
    [TotallyDisconnectedSpace K] (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup))
    (hR : IsUnit (p : R)) (M : ModuleCat.{uV} R) [Projective M] :
    Projective ((smoothTrivialFunctor R K).obj M) :=
  have := smoothInvariantsFunctor_preservesEpimorphisms R K hP hp hK hR
  (smoothTrivialAdjunction R K).map_projective M inferInstance

/-- Given `ProPInvariantsExactStatement`, the trivial smooth representation of `K` on an
`R`-module `M` projective relative to `R`-modules killed by `ℓ ^ m` is projective relative to
smooth representations killed by `ℓ ^ m`, for `K` and `p` as in
`smoothInvariantsFunctor_preservesEpimorphisms`. -/
theorem powTorsionProjective_smoothTrivialFunctor_obj
    (hP : ProPInvariantsExactStatement.{uK, uR, uV}) {p : ℕ} (hp : p.Prime) [CompactSpace K]
    [TotallyDisconnectedSpace K] (hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup))
    (hR : IsUnit (p : R)) {ℓ m : ℕ} {M : ModuleCat.{uV} R}
    (hM : DivisibleSystem.PowTorsionProjective ℓ m M) :
    DivisibleSystem.PowTorsionProjective ℓ m ((smoothTrivialFunctor R K).obj M) :=
  have := smoothInvariantsFunctor_preservesEpimorphisms R K hP hp hK hR
  DivisibleSystem.powTorsionProjective_obj_of_adjunction (smoothTrivialAdjunction R K) hM

end Trivial

section Subgroup

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Given `ProPInvariantsExactStatement`, the trivial smooth representation of a pro-`p`
subgroup `H` on a projective `R`-module is projective, for `p` invertible in `R`. -/
theorem projective_smoothTrivialFunctor_obj_of_isProPSubgroup
    (hP : ProPInvariantsExactStatement.{uG, uR, uV}) {p : ℕ} {H : Subgroup G}
    (hH : IsProPSubgroup p H) (hR : IsUnit (p : R)) (M : ModuleCat.{uV} R) [Projective M] :
    Projective ((smoothTrivialFunctor R H).obj M) :=
  have := hH.compactSpace
  have := hH.totallyDisconnectedSpace
  projective_smoothTrivialFunctor_obj R H hP hH.prime hH.isPGroup hR M

/-- Given `ProPInvariantsExactStatement`, the compact induction `c-Ind_H^G M` of the trivial
smooth representation of an open pro-`p` subgroup `H` on a projective `R`-module `M` is a
projective smooth representation of `G`, for `p` invertible in `R`. -/
theorem projective_smoothCompactInduction_smoothTrivialFunctor_obj
    (hP : ProPInvariantsExactStatement.{uG, uR, max uG uV}) {p : ℕ} {H : Subgroup G}
    (hH : IsProPSubgroup p H) (hHo : IsOpen (H : Set G)) (hR : IsUnit (p : R))
    (M : ModuleCat.{max uG uV} R) [Projective M] :
    Projective ((Induction.smoothCompactInduction.{uR, uG, uV} R H).obj
      ((smoothTrivialFunctor R H).obj M)) :=
  Induction.projective_smoothCompactInduction H hHo _
    (projective_smoothTrivialFunctor_obj_of_isProPSubgroup hP hH hR M)

end Subgroup

section CompactInduction

open SupercuspidalExt DivisibleSystem

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (hP : ProPInvariantsExactStatement.{u, u, u}) {p : ℕ}
  {H : Subgroup G} (hH : IsProPSubgroup p H) (hHo : IsOpen (H : Set G)) (hR : IsUnit (p : R))
  {ℓ : ℕ}

include hP hH hHo hR in
/-- Given `ProPInvariantsExactStatement`, compact induction `c-Ind_H^G M` from an open pro-`p`
subgroup `H` of the trivial representation on an `R`-module `M` projective relative to
`R`-modules killed by `ℓ ^ m` is projective relative to smooth representations killed by
`ℓ ^ m`, for `p` invertible in `R`. -/
theorem powTorsionProjective_compactInduction_smoothTrivialFunctor_obj {m : ℕ}
    {M : ModuleCat.{u} R} (hM : PowTorsionProjective ℓ m M) :
    PowTorsionProjective ℓ m ((compactInduction R G H).obj ((smoothTrivialFunctor R H).obj M)) :=
  have := hH.compactSpace
  have := hH.totallyDisconnectedSpace
  powTorsionProjective_compactInduction R hHo
    (powTorsionProjective_smoothTrivialFunctor_obj R H hP hH.prime hH.isPGroup hR hM)

include hP hH hHo hR in
/-- Given `ProPInvariantsExactStatement`, for an open pro-`p` subgroup `H`, `p` invertible in
`R` and a projective `R`-module `M`, the cokernel of multiplication by `ℓ ^ m` on
`c-Ind_H^G M` (the trivial representation on `M`, compactly induced) is projective relative to
smooth representations killed by `ℓ ^ m`. That this cokernel is killed by `ℓ ^ m` is the
published `powSMul_cokernel_powSMul`. -/
theorem powTorsionProjective_cokernel_compactInduction_smoothTrivialFunctor_obj (m : ℕ)
    (M : ModuleCat.{u} R) [Projective M] :
    PowTorsionProjective ℓ m (cokernel (powSMul ℓ m
      ((compactInduction R G H).obj ((smoothTrivialFunctor R H).obj M)))) :=
  powTorsionProjective_cokernel_powSMul
    (powTorsionProjective_compactInduction_smoothTrivialFunctor_obj hP hH hHo hR
      (powTorsionProjective_of_projective ℓ m M))

end CompactInduction

end Langlands.Cohomology
