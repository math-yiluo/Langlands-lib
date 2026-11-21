# Finite isolation of an ambient coefficient in the full-Levi packet

Waldspurger VIII.4.2, printed p. 330 (PDF p. 96), prescribes the section
coefficient at one class and makes it vanish at the other classes with the
same central character. This comparison implements the finite interpolation
step on the full-Levi orbit for any finite set of other classes.

`rationalFullLeviBaseRepresentative` uses the pulled-back ambient
representation itself, which belongs to its unitary orbit by twisting
with the trivial character. Its class is the image of the trivial-twist
ambient class under the full-Levi orbit homeomorphism.

For each class in the finite set, use the homeomorphism and surjectivity
of the representative map to choose an actual inducing representative.
Their smooth classes differ from the base class. The finite-value
interpolation theorem gives a coherent smooth section with the prescribed
product-induced value at the base representative and zero at each of the
chosen representatives. The coefficient identity compares these values
with the chosen ambient tensors. Injectivity of the coefficient tensor
map for each canonical irreducible admissible representative makes the
ambient tensors zero at the other chosen classes. The construction uses
the same carrier universe `uV` throughout.
